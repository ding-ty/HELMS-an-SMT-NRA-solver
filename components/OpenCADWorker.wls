(* Independent OpenCAD only. No reference answer is supplied to the worker. *)
started = SessionTime[];
$MaxExtraPrecision = Infinity;
arguments = $ScriptCommandLine;
position = FirstPosition[arguments, "--request"];
If[MissingQ[position] || First[position] >= Length[arguments], Exit[2]];
request = Quiet[Check[Import[arguments[[First[position]+1]], "RawJSON"], $Failed]];
If[! AssociationQ[request], Exit[2]];
resultPath = request["worker_result_path"];
If[AnyTrue[FileNameJoin[{DirectoryName[resultPath], #}] & /@
    {"worker_result.json", "worker_result.json.tmp", "solve_started.json", "solve_finished.json", "raw_answer.txt", "formula.wl", "wolfram_messages.log"},
    FileExistsQ], Exit[5]];
AtomicJSON[path_, value_] := Module[{tmp = path <> ".tmp"},
  Export[tmp, value, "RawJSON", CharacterEncoding -> "UTF-8"];
  RenameFile[tmp, path]; True];
result = <|"schema_version" -> 1, "actual_status" -> "error", "failure_kind" -> "input_error",
  "reason" -> "worker did not complete", "solve_seconds" -> 0., "verification_seconds" -> 0.,
  "runtime_identity" -> <|"wolfram_version" -> $Version, "system_id" -> $SystemID|>,
  "stage" -> "OpenCAD", "source_profile" -> "direct_generic_cylindrical_decomposition",
  "solver" -> "OpenCAD", "request_id" -> request["request_id"], "case_id" -> request["case_id"],
  "input_sha256" -> request["input_sha256"], "time_source" -> "SessionTime",
  "timing_basis" -> "OpenCAD_plus_returned_cell_witness_extraction;verification_separate",
  "max_extra_precision" -> "Infinity"|>;
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


decoded = Catch[Module[{data, strings, names, variables, p, c, inputHash},
  If[request["solver"] =!= "OpenCAD" || ! NumberQ[request["timeout_seconds"]] ||
    ! TrueQ[request["timeout_seconds"] > 0], FailInput["invalid solver or budget"]];
  If[KeyExistsQ[request, "expected_status"], FailInput["reference answer must not be supplied"]];
  inputHash = IntegerString[FileHash[request["input_path"], "SHA256"], 16, 64];
  If[inputHash =!= request["input_sha256"], FailInput["input hash mismatch"]];
  data = Import[request["input_path"], "RawJSON"];
  If[! AssociationQ[data] || Sort[Keys[data]] =!= {"clauses", "polynomials", "variables"}, FailInput["invalid input keys"]];
  strings = data["variables"];
  If[! ListQ[strings] || ! And @@ (StringQ /@ strings) || Length[DeleteDuplicates[strings]] != Length[strings], FailInput["invalid variable list"]];
  variables = Table[Unique["InputVariable$"], {Length[strings]}];
  names = Association[Thread[strings -> variables]];
  If[! ListQ[data["polynomials"]], FailInput["invalid polynomial list"]];
  p = Expand[DecodeNode[#, names]] & /@ data["polynomials"];
  c = data["clauses"];
  If[! ListQ[c] || ! And @@ (ListQ /@ c), FailInput["invalid CNF"]];
  If[! And @@ (MatchQ[#, {_Integer, 1 | -1}] && 1 <= #[[1]] <= Length[p] & /@ Flatten[c, 1]), FailInput["invalid atom"]];
  <|"formula" -> FormulaOf[p, c], "variables" -> variables, "names" -> strings|>
], "input"];
If[AssociationQ[decoded] && KeyExistsQ[decoded, "input_error"], result["reason"] = decoded["input_error"],
  If[! AssociationQ[decoded], result["reason"] = "input decoding failed",
    formula = decoded["formula"]; variables = decoded["variables"];
    result["variable_order"] = decoded["names"];
    formulaPath = FileNameJoin[{DirectoryName[resultPath], "formula.wl"}];
    Export[formulaPath, ToString[formula, InputForm, PageWidth -> Infinity], "Text"];
    result["formula_sha256"] = IntegerString[FileHash[formulaPath, "SHA256"], 16, 64];
    messagePath = FileNameJoin[{DirectoryName[resultPath], "wolfram_messages.log"}];
    stream = OpenWrite[messagePath, CharacterEncoding -> "UTF-8", PageWidth -> Infinity];
    If[Head[stream] =!= OutputStream, Exit[4]];
    Block[{$Messages = {stream}, $MessageList = {}},
      SeedRandom[request["seed"]];
      result["startup_seconds"] = N[SessionTime[] - started];
      model = None; extractionSeconds = 0.; raw = Missing["NotReturned"];
      marker = AtomicJSON[FileNameJoin[{DirectoryName[resultPath], "solve_started.json"}],
        <|"request_id" -> request["request_id"], "phase" -> "solve_started", "timeout_seconds" -> request["timeout_seconds"]|>];
      If[! TrueQ[marker], Exit[4]];
      solveStart = SessionTime[];
      answer = Check[TimeConstrained[
        If[formula === True,
          model = Association[Thread[variables -> ConstantArray[0, Length[variables]]]];
          <|"decision" -> "sat", "basis" -> "exact_constant_formula"|>,
        If[formula === False, <|"decision" -> "unsat", "basis" -> "exact_constant_formula"|>,
          raw = GenericCylindricalDecomposition[formula, variables];
          If[raw === {False, False}, <|"decision" -> "unsat", "basis" -> "OpenCAD_empty_decomposition"|>,
          If[! MatchQ[raw, {_, _}] || raw[[1]] === False,
            <|"decision" -> "unknown", "basis" -> "no_certified_full_dimensional_cell"|>,
            extractStart = SessionTime[];
            instances = FindInstance[raw[[1]], variables, Reals, 1];
            extractionSeconds = N[SessionTime[] - extractStart];
            If[MatchQ[instances, {_List ..}], model = Association[First[instances]]];
            <|"decision" -> If[AssociationQ[model], "sat", "unknown"], "basis" -> "OpenCAD_cell_witness"|>]]]],
        request["timeout_seconds"], <|"decision" -> "timeout", "basis" -> "solve_budget_exhausted"|>],
        <|"decision" -> "error", "basis" -> "wolfram_message"|>];
      result["solve_seconds"] = N[SessionTime[] - solveStart];
      AtomicJSON[FileNameJoin[{DirectoryName[resultPath], "solve_finished.json"}],
        <|"request_id" -> request["request_id"], "phase" -> "solve_finished", "solve_seconds" -> result["solve_seconds"]|>];
      result["witness_extraction_seconds"] = extractionSeconds;
      result["wolfram_messages"] = ToString[#, InputForm] & /@ $MessageList;
      If[! AssociationQ[answer], answer = <|"decision" -> "error", "basis" -> "invalid_return"|>];
      result["actual_status"] = answer["decision"];
      result["reported_status"] = answer["decision"];
      result["decision_basis"] = answer["basis"];
      result["failure_kind"] = Switch[answer["decision"], "timeout", "solve_timeout", "error", "solver_evaluation_error", "unknown", "undecided", _, ""];
      result["reason"] = Switch[answer["decision"], "timeout", "full solve budget exhausted", "error", "Wolfram evaluation emitted a message; see preserved log", "unknown", "no validated decision", _, ""];
      rawPath = FileNameJoin[{DirectoryName[resultPath], "raw_answer.txt"}];
      rawWritten = Check[Export[rawPath, ToString[raw, InputForm, PageWidth -> Infinity], "Text", CharacterEncoding -> "UTF-8"]; True, False];
      If[TrueQ[rawWritten], result["raw_answer_sha256"] = IntegerString[FileHash[rawPath, "SHA256"], 16, 64],
        result["actual_status"] = "error"; result["failure_kind"] = "evidence_write_error"];
      If[result["actual_status"] === "sat",
        verifyStart = SessionTime[];
        valid = Check[TimeConstrained[ExactModelQ[formula, variables, model], 30., $Aborted], $Failed];
        result["verification_seconds"] = N[SessionTime[] - verifyStart];
        result["model_verified"] = TrueQ[valid];
        result["model_validation"] = <|"valid" -> TrueQ[valid], "exact" -> True, "method" -> "exact_original_formula_substitution"|>;
        If[AssociationQ[model], result["model_values"] = Association[Thread[decoded["names"] ->
          (ToString[#, InputForm] & /@ Lookup[model, variables, Missing["NoValue"]])]]];
        If[! TrueQ[valid], result["actual_status"] = "error";
          result["failure_kind"] = If[valid === $Aborted, "verification_timeout", "invalid_model"];
          result["reason"] = "SAT witness failed exact verification"]];
      If[result["actual_status"] === "unsat", result["unsat_independently_verified"] = False];
    ];
    Close[stream];
  ]
];
If[! TrueQ[Quiet[Check[AtomicJSON[resultPath, result], False]]], Exit[3]];
Exit[0];
