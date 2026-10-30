(* Machine protocol: a fresh kernel, one request, one atomic JSON result.
   No expected benchmark status is supplied to or read by the solver. *)
started = AbsoluteTime[];
arguments = If[ListQ[$ScriptCommandLine] && Length[$ScriptCommandLine] > 0,
  $ScriptCommandLine, $CommandLine];
requestPosition = FirstPosition[arguments, "--request"];
If[MissingQ[requestPosition] || First[requestPosition] >= Length[arguments], Exit[2]];
requestPath = arguments[[First[requestPosition] + 1]];
request = Quiet[Check[Import[requestPath, "RawJSON", CharacterEncoding -> "UTF-8"], $Failed]];
If[! AssociationQ[request] || ! StringQ[Lookup[request, "worker_result_path", Null]], Exit[2]];
resultPath = request["worker_result_path"];
packageRoot = DirectoryName[DirectoryName[$InputFileName]];
result = <|"actual_status" -> "error", "solve_seconds" -> 0., "startup_seconds" -> 0.,
  "stage" -> "input", "reason" -> "worker did not complete"|>;

FailInput[message_] := Throw[<|"input_error" -> message|>, "input"];
ExactInteger[s_] := If[StringQ[s] && StringMatchQ[s, RegularExpression["-?(0|[1-9][0-9]*)"]],
  If[StringStartsQ[s, "-"], -FromDigits[StringDrop[s, 1]], FromDigits[s]], FailInput["invalid integer"]];
DecodeNode[node_Association, names_Association] := Module[{op, args, numerator, denominator, exponent},
  op = Lookup[node, "op", ""];
  Switch[op,
    "int", ExactInteger[Lookup[node, "value", Null]],
    "rat", numerator = ExactInteger[Lookup[node, "numerator", Null]];
      denominator = ExactInteger[Lookup[node, "denominator", Null]];
      If[denominator == 0, FailInput["zero denominator"]]; numerator/denominator,
    "var", If[KeyExistsQ[names, Lookup[node, "name", Null]], names[node["name"]],
      FailInput["undeclared variable"]],
    "add" | "mul", args = Lookup[node, "args", Null];
      If[! ListQ[args], FailInput["operation args must be a list"]];
      args = DecodeNode[#, names] & /@ args;
      If[op === "add", Plus @@ args, Times @@ args],
    "pow", exponent = Lookup[node, "exponent", Null];
      If[! IntegerQ[exponent] || exponent < 0, FailInput["polynomial exponent must be a nonnegative integer"]];
      DecodeNode[Lookup[node, "base", Null], names]^exponent,
    _, FailInput["unsupported AST operation"]]
];
DecodeNode[_, _] := FailInput["AST node must be an object"];

decoded = Catch[Module[{data, strings, names, polynomials, clauses, variables},
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
  <|"polynomials" -> polynomials, "clauses" -> clauses,
    "variables" -> variables, "names" -> strings|>
], "input"];

If[AssociationQ[decoded] && KeyExistsQ[decoded, "input_error"],
  result["reason"] = decoded["input_error"],
  solverSource = Switch[Lookup[request, "solver", ""],
    "HELMS", FileNameJoin[{packageRoot, "solvers", "paper solvers", "HELMS.wl"}],
    "2D-LS", FileNameJoin[{packageRoot, "solvers", "paper solvers", "2DLS.wl"}],
    "V1" | "V2" | "V3" | "V4" | "V5",
      FileNameJoin[{packageRoot, "solvers", "paper solvers", request["solver"] <> ".wl"}],
    "LS-WL", FileNameJoin[{packageRoot, "solvers", "baseline solvers", "LSwolfram.wl"}],
    _, $Failed];
  loaded = If[StringQ[solverSource], Quiet[Check[Get[solverSource]; True, False]], False];
  If[! TrueQ[loaded],
    result["reason"] = "solver source did not load",
    config = Lookup[request, "worker_config", <||>];
    If[! AssociationQ[config], config = <||>];
    If[MemberQ[{"2D-LS", "HELMS"}, request["solver"]],
      config = Join[config, <|"experiment_timeout_seconds" -> request["timeout_seconds"]|>]];
    SeedRandom[request["seed"]];
    result["startup_seconds"] = N[AbsoluteTime[] - started];
    (* Keep Check's failure semantics and record messages instead of hiding
       the evidence in Quiet. Each request has its own diagnostic sidecar. *)
    messageLogPath = FileNameJoin[{DirectoryName[resultPath], "wolfram_messages.log"}];
    messageStream = Quiet[Check[OpenWrite[messageLogPath, CharacterEncoding -> "UTF-8",
      PageWidth -> Infinity], $Failed]];
    solveStart = AbsoluteTime[];
    If[MemberQ[{"2D-LS", "HELMS"}, request["solver"]],
      config = Join[config, <|"experiment_deadline_session_seconds" ->
        SessionTime[] + request["timeout_seconds"]|>]];
    Block[{$Messages = If[Head[messageStream] === OutputStream, {messageStream}, $Messages],
        $MessageList = {}},
      answer = Check[
        TimeConstrained[
          Switch[request["solver"],
            "HELMS", HELMS`Solve[decoded["polynomials"], decoded["clauses"], decoded["variables"],
              "Config" -> config, "TimeLimit" -> Infinity],
            "2D-LS", TwoDLS`Solve[decoded["polynomials"], decoded["clauses"], decoded["variables"],
              "Config" -> config, "TimeLimit" -> Infinity],
            "V1", V1`Solve[decoded["polynomials"], decoded["clauses"], decoded["variables"],
              "Config" -> config, "TimeLimit" -> Infinity],
            "V2", V2`Solve[decoded["polynomials"], decoded["clauses"], decoded["variables"],
              "Config" -> config, "TimeLimit" -> Infinity],
            "V3", V3`Solve[decoded["polynomials"], decoded["clauses"], decoded["variables"],
              "Config" -> config, "TimeLimit" -> Infinity],
            "V4", V4`Solve[decoded["polynomials"], decoded["clauses"], decoded["variables"],
              "Config" -> config, "TimeLimit" -> Infinity],
            "V5", V5`Solve[decoded["polynomials"], decoded["clauses"], decoded["variables"],
              "Config" -> config, "TimeLimit" -> Infinity],
            "LS-WL", LSwolfram`Solve[decoded["polynomials"], decoded["clauses"], decoded["variables"],
              "Config" -> config, "TimeLimit" -> Infinity],
            _, <|"status" -> "error", "reason" -> "unknown solver tool"|>], request["timeout_seconds"],
          <|"status" -> "timeout", "stage" -> "timeout", "reason" -> "solve budget exhausted"|>],
        <|"status" -> "error", "stage" -> "kernel", "reason" -> "Wolfram evaluation emitted an error"|>];
      solveMessageNames = ToString[#, InputForm] & /@ $MessageList];
    result["solve_seconds"] = N[AbsoluteTime[] - solveStart];
    If[Head[messageStream] === OutputStream, Close[messageStream]];
    result["wolfram_messages"] = solveMessageNames;
    If[Head[messageStream] === OutputStream, result["wolfram_message_log"] = messageLogPath];
    If[! AssociationQ[answer], answer = <|"status" -> "error", "reason" -> "invalid solver result"|>];
    result["actual_status"] = Lookup[answer, "status", "error"];
    result["stage"] = Lookup[answer, "stage", "unknown"];
    result["reason"] = Lookup[answer, "reason", ""];
    result["source_profile"] = Switch[request["solver"],
      "LS-WL", "LS-WL", "2D-LS", "2D-LS", _, "HELMS"];
    result["solver_metadata"] = Join[
      If[AssociationQ[Lookup[answer, "solver_metadata", <||>]],
        Lookup[answer, "solver_metadata", <||>], <||>],
      <|"source_profile" -> result["source_profile"],
      "cache_enabled" -> TrueQ[Lookup[config, "cache_enabled", True]],
      "cache_max_entries" -> Lookup[config, "cache_max_entries", 20000],
      "wolfram_version" -> $Version, "system_id" -> $SystemID|>];
    If[request["solver"] === "LS-WL" && KeyExistsQ[answer, "restarts_attempted"],
      result["solver_metadata"] = Join[result["solver_metadata"],
        <|"restarts_attempted" -> answer["restarts_attempted"]|>]];
    If[KeyExistsQ[answer, "assignment"],
      result["model_verified"] = TrueQ[Switch[request["solver"],
        "HELMS", HELMSLocal`ModelQ[decoded["polynomials"], decoded["clauses"], decoded["variables"], answer["assignment"]],
        "2D-LS", TwoDLSCore`ModelQ[decoded["polynomials"], decoded["clauses"], decoded["variables"], answer["assignment"]],
        _, PaperSolvers`ModelQ[decoded["polynomials"], decoded["clauses"], decoded["variables"], answer["assignment"]]]];
      result["model_values"] = Association[Thread[decoded["names"] ->
        (ToString[#, InputForm] & /@ Lookup[answer["assignment"], decoded["variables"]])]];
      result["solver_metadata"]["model_verified"] = result["model_verified"];
      result["solver_metadata"]["model_values"] = result["model_values"]];
    If[KeyExistsQ[answer, "num_fail_cells_estimate"],
      result["num_fail_cells_estimate"] = answer["num_fail_cells_estimate"]];
  ]
];
result["startup_seconds"] = Max[0., N[result["startup_seconds"]]];
result["solve_seconds"] = Max[0., N[result["solve_seconds"]]];
temporaryPath = resultPath <> ".tmp";
written = Quiet[Check[
  Export[temporaryPath, result, "RawJSON", CharacterEncoding -> "UTF-8"];
  RenameFile[temporaryPath, resultPath, OverwriteTarget -> True]; True, False]];
If[TrueQ[written], Exit[0], Exit[3]];
