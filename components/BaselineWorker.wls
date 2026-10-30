(* A fresh kernel evaluates one independent baseline request.  Expected benchmark
   labels are neither supplied to this protocol nor consulted by either solver. *)
started = AbsoluteTime[];
arguments = If[ListQ[$ScriptCommandLine] && Length[$ScriptCommandLine] > 0,
  $ScriptCommandLine, $CommandLine];
requestPosition = FirstPosition[arguments, "--request"];
If[MissingQ[requestPosition] || First[requestPosition] >= Length[arguments], Exit[2]];
requestPath = arguments[[First[requestPosition] + 1]];
request = Quiet[Check[Import[requestPath, "RawJSON", CharacterEncoding -> "UTF-8"], $Failed]];
If[! AssociationQ[request] || ! StringQ[Lookup[request, "worker_result_path", Null]], Exit[2]];
resultPath = request["worker_result_path"];
(* Each worker owns a fresh attempt directory. Duplicate execution must never
   overwrite earlier result or diagnostic evidence. *)
If[AnyTrue[Join[{resultPath, resultPath <> ".tmp"},
    FileNameJoin[{DirectoryName[resultPath], #}] & /@ {"solve_started.json", "solve_started.json.tmp",
      "solve_finished.json", "solve_finished.json.tmp", "raw_answer.txt", "wolfram_messages.log"}],
    FileExistsQ], Exit[5]];
packageRoot = DirectoryName[DirectoryName[$InputFileName]];
result = <|"schema_version" -> 1, "actual_status" -> "error", "stage" -> "input",
  "reason" -> "worker did not complete", "failure_kind" -> "input_error",
  "solve_seconds" -> 0., "verification_seconds" -> 0., "startup_seconds" -> 0.,
  "runtime_identity" -> <|"wolfram_version" -> $Version, "system_id" -> $SystemID|>|>;
Scan[If[KeyExistsQ[request, #], result[#] = request[#]] &, {"request_id", "case_id", "solver", "input_sha256"}];
AtomicJSON[path_, value_] := Module[{tmp = path <> ".tmp"},
  Export[tmp, value, "RawJSON", CharacterEncoding -> "UTF-8"];
  RenameFile[tmp, path, OverwriteTarget -> True]; True];

FailInput[message_] := Throw[<|"input_error" -> message|>, "input"];
ExactInteger[s_] := If[StringQ[s] && StringMatchQ[s, RegularExpression["-?(0|[1-9][0-9]*)"]],
  If[StringStartsQ[s, "-"], -FromDigits[StringDrop[s, 1]], FromDigits[s]], FailInput["invalid integer"]];
NodeKeysQ[node_, required_] := Sort[Keys[node]] === Sort[required];
DecodeNode[node_Association, names_Association] := Module[{op, args, numerator, denominator, exponent},
  op = Lookup[node, "op", ""];
  Switch[op,
    "int", If[! NodeKeysQ[node, {"op", "value"}], FailInput["invalid integer node"]];
      ExactInteger[Lookup[node, "value", Null]],
    "rat", If[! NodeKeysQ[node, {"op", "numerator", "denominator"}], FailInput["invalid rational node"]];
      numerator = ExactInteger[Lookup[node, "numerator", Null]];
      denominator = ExactInteger[Lookup[node, "denominator", Null]];
      If[denominator == 0, FailInput["zero denominator"]]; numerator/denominator,
    "var", If[! NodeKeysQ[node, {"op", "name"}], FailInput["invalid variable node"]];
      If[KeyExistsQ[names, Lookup[node, "name", Null]], names[node["name"]], FailInput["undeclared variable"]],
    "add" | "mul", If[! NodeKeysQ[node, {"op", "args"}], FailInput["invalid operation node"]];
      args = Lookup[node, "args", Null];
      If[! ListQ[args], FailInput["operation args must be a list"]];
      args = DecodeNode[#, names] & /@ args;
      If[op === "add", Plus @@ args, Times @@ args],
    "pow", If[! NodeKeysQ[node, {"op", "base", "exponent"}], FailInput["invalid power node"]];
      exponent = Lookup[node, "exponent", Null];
      If[! IntegerQ[exponent] || exponent < 0, FailInput["polynomial exponent must be a nonnegative integer"]];
      DecodeNode[Lookup[node, "base", Null], names]^exponent,
    _, FailInput["unsupported AST operation"]]
];
DecodeNode[_, _] := FailInput["AST node must be an object"];
FormulaOf[p_, c_] := And @@ (Function[clause,
  Or @@ (Function[atom, atom[[2]] p[[atom[[1]]]] > 0] /@ clause)] /@ c);
ExactRealQ[x_] := FreeQ[x, _Real | _Complex] && TrueQ[Element[x, Reals]];
ExactModelQ[formula_, variables_, assignment_] := AssociationQ[assignment] &&
  And @@ (KeyExistsQ[assignment, #] & /@ variables) &&
  And @@ (ExactRealQ /@ Lookup[assignment, variables]) && TrueQ[formula /. Normal[assignment]];

(* The source assumes nonconstant indexed polynomials.  Fold only constant
   truth values and retain all remaining literals, clauses, and variable order.
   This is not LS, MCSAT-based preprocessing, or an alternate decision solver. *)
LiMbSInput[p_, c_] := Module[{nonconstant, kept, map, clauses, current, truth, atoms, a},
  nonconstant = (! NumberQ[#] &) /@ p;
  kept = Pick[Range[Length[p]], nonconstant];
  map = Association[Thread[kept -> Range[Length[kept]]]];
  clauses = {};
  Do[current = {}; truth = False;
    Do[If[TrueQ[nonconstant[[a[[1]]]]], AppendTo[current, a[[2]] map[a[[1]]]],
      If[TrueQ[a[[2]] p[[a[[1]]]] > 0], truth = True]], {a, atoms}];
    If[! truth, AppendTo[clauses, current]], {atoms, c}];
  <|"polynomials" -> p[[kept]], "clauses" -> clauses,
    "constant_polynomials_removed" -> Length[p] - Length[kept]|>
];

decoded = Catch[Module[{data, strings, names, polynomials, clauses, variables},
  If[! StringQ[Lookup[request, "input_path", Null]], FailInput["missing input path"]];
  If[! MemberQ[{"LiMbS", "OpenCAD"}, Lookup[request, "solver", Null]], FailInput["unsupported solver"]];
  If[! NumberQ[Lookup[request, "timeout_seconds", Null]] || ! TrueQ[request["timeout_seconds"] > 0],
    FailInput["timeout must be positive"]];
  If[! IntegerQ[Lookup[request, "seed", Null]], FailInput["seed must be an integer"]];
  inputHash = Quiet[Check[IntegerString[FileHash[request["input_path"], "SHA256"], 16, 64], $Failed]];
  If[! StringQ[inputHash], FailInput["input file could not be hashed"]];
  If[KeyExistsQ[request, "input_sha256"] && request["input_sha256"] =!= inputHash,
    FailInput["input hash mismatch"]];
  result["input_sha256"] = inputHash;
  data = Quiet[Check[Import[request["input_path"], "RawJSON", CharacterEncoding -> "UTF-8"], $Failed]];
  If[! AssociationQ[data] || Sort[Keys[data]] =!= {"clauses", "polynomials", "variables"},
    FailInput["input must contain only variables, polynomials, clauses"]];
  strings = data["variables"];
  If[! ListQ[strings] || ! And @@ (StringQ /@ strings) || Length[DeleteDuplicates[strings]] != Length[strings],
    FailInput["invalid variable list"]];
  variables = Table[Unique["InputVariable$"], {Length[strings]}];
  names = Association[Thread[strings -> variables]];
  If[! ListQ[data["polynomials"]], FailInput["invalid polynomial list"]];
  polynomials = Expand[DecodeNode[#, names]] & /@ data["polynomials"];
  clauses = data["clauses"];
  If[! ListQ[clauses] || ! And @@ (ListQ /@ clauses), FailInput["invalid clauses"]];
  If[! And @@ (MatchQ[#, {_Integer, 1 | -1}] && 1 <= #[[1]] <= Length[polynomials] & /@
      Flatten[clauses, 1]), FailInput["invalid atom index or sign"]];
  <|"polynomials" -> polynomials, "clauses" -> clauses, "variables" -> variables,
    "names" -> strings, "formula" -> FormulaOf[polynomials, clauses]|>
], "input"];

If[AssociationQ[decoded] && KeyExistsQ[decoded, "input_error"], result["reason"] = decoded["input_error"],
  messagePath = FileNameJoin[{DirectoryName[resultPath], "wolfram_messages.log"}];
  messageStream = Quiet[Check[OpenWrite[messagePath, CharacterEncoding -> "UTF-8", PageWidth -> Infinity], $Failed]];
  If[Head[messageStream] =!= OutputStream, result["reason"] = "cannot open diagnostic sidecar",
    Block[{$Messages = {messageStream}, $MessageList = {}},
      sourcePath = FileNameJoin[{packageRoot, "solvers", "baseline solvers", "LiMbS.wl"}];
      loaded = If[request["solver"] === "LiMbS", Check[Get[sourcePath];
        Length[DownValues[LiMbS`NRASolver]] > 0, False], True];
      result["source_load_messages"] = ToString[#, InputForm] & /@ $MessageList;
      If[! TrueQ[loaded], result["reason"] = "solver source did not load";
        result["failure_kind"] = "source_load_error",
        SeedRandom[request["seed"]];
        formula = decoded["formula"]; variables = decoded["variables"];
        result["variable_order"] = decoded["names"];
        result["source_profile"] = If[request["solver"] === "LiMbS",
          "LiMbS", "direct_generic_cylindrical_decomposition"];
        result["source_variant"] = If[request["solver"] === "LiMbS", "LiMbS", "OpenCAD_direct"];
        result["timing_basis"] = "independent_baseline_full_solve_budget_includes_OpenCAD_cell_witness_extraction";
        If[request["solver"] === "LiMbS",
          result["library_sha256"] = IntegerString[FileHash[sourcePath, "SHA256"], 16, 64]];
        result["startup_seconds"] = N[AbsoluteTime[] - started];
        $MessageList = {}; model = None; extractionSeconds = 0.;
        markerReady = Check[AtomicJSON[FileNameJoin[{DirectoryName[resultPath], "solve_started.json"}],
          <|"phase" -> "solve_started", "request_id" -> Lookup[request, "request_id", Null],
            "timeout_seconds" -> request["timeout_seconds"]|>], False];
        If[! TrueQ[markerReady], Exit[4]];
        solveStart = AbsoluteTime[];
        answer = Check[TimeConstrained[
          If[formula === True, model = Association[Thread[variables -> ConstantArray[0, Length[variables]]]];
            <|"decision" -> "sat", "basis" -> "exact_constant_formula"|>,
          If[formula === False, <|"decision" -> "unsat", "basis" -> "exact_constant_formula"|>,
          If[request["solver"] === "LiMbS",
            sourceInput = LiMbSInput[decoded["polynomials"], decoded["clauses"]];
            result["constant_polynomials_removed"] = sourceInput["constant_polynomials_removed"];
            raw = LiMbS`NRASolver[sourceInput["clauses"], sourceInput["polynomials"], variables];
            If[MatchQ[raw, {"Sat", _Association}], model = raw[[2]]];
            <|"raw" -> raw, "decision" -> Which[MatchQ[raw, {"Sat", _Association}], "sat",
              raw === {"Unsat"}, "unsat", True, "unknown"], "basis" -> "standalone_NRASolver"|>,
            raw = GenericCylindricalDecomposition[formula, variables];
            If[raw === {False, False}, <|"raw" -> raw, "decision" -> "unsat", "basis" -> "OpenCAD_empty_decomposition"|>,
              If[! MatchQ[raw, {_, _}] || raw[[1]] === False,
                <|"raw" -> raw, "decision" -> "unknown", "basis" -> "no_full_dimensional_cell"|>,
                extractStart = AbsoluteTime[];
                instances = FindInstance[raw[[1]], variables, Reals, 1];
                extractionSeconds = N[AbsoluteTime[] - extractStart];
                If[MatchQ[instances, {_List ..}], model = Association[First[instances]]];
                <|"raw" -> raw, "decision" -> If[AssociationQ[model], "sat", "unknown"],
                  "basis" -> "OpenCAD_cell_witness"|>]]]]],
          request["timeout_seconds"], <|"decision" -> "timeout", "basis" -> "solve_budget_exhausted"|>],
          <|"decision" -> "error", "basis" -> "wolfram_message"|>];
        result["solve_seconds"] = N[AbsoluteTime[] - solveStart];
        markerFinished = Check[AtomicJSON[FileNameJoin[{DirectoryName[resultPath], "solve_finished.json"}],
          <|"phase" -> "solve_finished", "request_id" -> Lookup[request, "request_id", Null],
            "solve_seconds" -> result["solve_seconds"]|>], False];
        If[! TrueQ[markerFinished], Exit[4]];
        result["witness_extraction_seconds"] = extractionSeconds;
        result["wolfram_messages"] = ToString[#, InputForm] & /@ $MessageList;
        If[! AssociationQ[answer], answer = <|"decision" -> "error", "basis" -> "invalid_worker_answer"|>];
        result["actual_status"] = Lookup[answer, "decision", "error"];
        result["reported_status"] = result["actual_status"];
        result["stage"] = request["solver"];
        result["decision_basis"] = Lookup[answer, "basis", "unknown"];
        result["reason"] = Switch[result["actual_status"], "timeout", "solve budget exhausted",
          "error", "Wolfram evaluation emitted a message", "unknown", "solver returned no validated decision", _, ""];
        result["failure_kind"] = Switch[result["actual_status"], "error", "solver_evaluation_error",
          "timeout", "solve_timeout", "unknown", "undecided", _, ""];
        If[KeyExistsQ[answer, "raw"],
          rawPath = FileNameJoin[{DirectoryName[resultPath], "raw_answer.txt"}];
          rawWritten = Check[Export[rawPath, ToString[answer["raw"], InputForm, PageWidth -> Infinity],
            "Text", CharacterEncoding -> "UTF-8"]; True, False];
          If[TrueQ[rawWritten], result["raw_answer_path"] = rawPath;
            result["raw_answer_sha256"] = IntegerString[FileHash[rawPath, "SHA256"], 16, 64],
            result["actual_status"] = "error"; result["failure_kind"] = "evidence_write_error";
            result["reason"] = "cannot preserve raw solver output"]];
        If[result["actual_status"] === "sat",
          verifyStart = AbsoluteTime[]; $MessageList = {};
          verification = Check[TimeConstrained[ExactModelQ[formula, variables, model],
            Lookup[request, "verification_timeout_seconds", 30.], $Aborted], $Failed];
          result["verification_seconds"] = N[AbsoluteTime[] - verifyStart];
          result["verification_messages"] = ToString[#, InputForm] & /@ $MessageList;
          result["model_verified"] = TrueQ[verification];
          result["model_validation_type"] = "exact_original_formula_substitution";
          result["model_validation"] = <|"valid" -> TrueQ[verification], "exact" -> True,
            "method" -> "exact_original_formula_substitution"|>;
          If[AssociationQ[model], result["model_values"] = Association[Thread[decoded["names"] ->
            (ToString[#, InputForm] & /@ Lookup[model, variables, Missing["NoValue"]])]]];
          If[! TrueQ[verification], result["actual_status"] = "error";
            result["failure_kind"] = If[verification === $Aborted, "verification_timeout", "invalid_model"];
            result["reason"] = "returned SAT model was not verified against the original exact formula"]];
        If[result["actual_status"] === "unsat", result["unsat_independently_verified"] = False];
      ]
    ];
    Close[messageStream]; result["wolfram_message_log"] = messagePath;
  ]
];
result["startup_seconds"] = Max[0., N[result["startup_seconds"]]];
result["solve_seconds"] = Max[0., N[result["solve_seconds"]]];
result["verification_seconds"] = Max[0., N[result["verification_seconds"]]];
temporaryPath = resultPath <> ".tmp";
written = Quiet[Check[Export[temporaryPath, result, "RawJSON", CharacterEncoding -> "UTF-8"];
  RenameFile[temporaryPath, resultPath, OverwriteTarget -> True]; True, False]];
If[TrueQ[written], Exit[0], Exit[3]];
