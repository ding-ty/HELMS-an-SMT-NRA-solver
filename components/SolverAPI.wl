(* Exact input adapters and the common calling interface. *)
BeginPackage["HELMSSolverAPI`"];
SolveEncoded::usage = "Internal input adapter for the public solver tools.";
SolveFormula::usage = "Internal strict polynomial formula adapter for the public solver tools.";
Begin["`Private`"];

$DefaultConfig = Quiet[Check[
  Import[FileNameJoin[{DirectoryName[DirectoryName[$InputFileName]], "config", "run_config.json"}],
    "RawJSON", CharacterEncoding -> "UTF-8"]["worker"], $Failed]];
$TwoDLSDefaultConfig = Quiet[Check[
  Import[FileNameJoin[{DirectoryName[DirectoryName[$InputFileName]], "config", "2dls_config.json"}],
    "RawJSON", CharacterEncoding -> "UTF-8"]["worker"], $Failed]];

$LSWLDefaultConfig = Quiet[Check[
  Import[FileNameJoin[{DirectoryName[DirectoryName[$InputFileName]], "config", "lswl_config.json"}],
    "RawJSON", CharacterEncoding -> "UTF-8"]["worker"], $Failed]];

InvalidInput[reason_String] := <|"status" -> "error", "stage" -> "input", "reason" -> reason|>;
VariablesQ[v_List] := DuplicateFreeQ[v] &&
  AllTrue[v, MatchQ[#, _Symbol] && ! NumericQ[#] && ! MemberQ[{True, False, Null}, #] &];
VariablesQ[_] := False;
RationalPolynomialQ[p_, v_List] := FreeQ[p, _Real] && PolynomialQ[p, v] &&
  Complement[Variables[{p}], v] === {} &&
  AllTrue[If[v === {}, {p}, Last /@ CoefficientRules[p, v]], IntegerQ[#] || Head[#] === Rational &];
EncodedQ[p_List, c_List, v_List] := VariablesQ[v] && AllTrue[p, RationalPolynomialQ[#, v] &] &&
  AllTrue[c, ListQ] && AllTrue[Flatten[c, 1],
    MatchQ[#, {_Integer, 1 | -1}] && 1 <= #[[1]] <= Length[p] &];
EncodedQ[___] := False;

ResolveConfig[overrides_, tool_: "HELMS"] := Module[{defaults},
  defaults = Switch[tool, "2D-LS", $TwoDLSDefaultConfig, "LS-WL", $LSWLDefaultConfig, _, $DefaultConfig];
  If[AssociationQ[overrides] && AssociationQ[defaults], Join[defaults, overrides], $Failed]
];
ValidTimeQ[seconds_] := seconds === Infinity ||
  (NumberQ[seconds] && TrueQ[0 < seconds < Infinity]);
WithinTime[seconds_, computation_Function] := If[seconds === Infinity, computation[],
  TimeConstrained[computation[], seconds,
    <|"status" -> "timeout", "stage" -> "timeout", "reason" -> "solve budget exhausted"|>]];

RunTool[p_, c_, v_, tool_, cfg_] := If[tool === "2D-LS",
  TwoDLSCore`SolveProblem[p, c, v, tool, cfg],
  If[MemberQ[{"V1", "V2", "V3", "V4", "V5", "LS-WL"}, tool],
    PaperSolvers`SolveProblem[p, c, v, tool, cfg], InvalidInput["unknown solver tool"]]];

RunEncoded[p_List, c_List, v_List, overrides_, seconds_, computation_Function, tool_: "HELMS"] := (
  If[! ValidTimeQ[seconds], Return[InvalidInput["TimeLimit must be a positive number or Infinity."]]];
  WithinTime[seconds, Function[Null, Module[{cfg},
    If[! EncodedQ[p, c, v], Return[InvalidInput[
      "Expected exact rational polynomials, distinct symbolic variables and pair-CNF atoms {index, sign}, with sign 1 or -1."]]];
    cfg = ResolveConfig[overrides, tool];
    If[! AssociationQ[cfg], Return[InvalidInput["Config must be an association and the default configuration must be available."]]];
    If[tool === "2D-LS" && seconds =!= Infinity,
      cfg = Join[cfg, <|"experiment_timeout_seconds" -> seconds,
        "experiment_deadline_session_seconds" -> SessionTime[] + seconds|>]];
    computation[cfg]]]]
);

SolveEncoded[p_List, c_List, v_List, tool_String, overrides_, seconds_] :=
  RunEncoded[p, c, v, overrides, seconds, Function[config, RunTool[p, c, v, tool, config]], tool];

(* Positive Boolean formulas are converted without calling a decision procedure.
   In pair-CNF, {i,s} denotes s*polynomials[[i]]>0. No preprocessing is
   applied to callers that already provide this encoding. *)
EncodeFormula[formula_, v_List] := Module[{polynomials = {}, tag, convert, disjoin, clauses},
  tag = Unique["formulaInput$"];
  disjoin[left_, right_] := If[left === {} || right === {}, {},
    Flatten[Table[Join[a, b], {a, left}, {b, right}], 1]];
  convert[f_] := Which[
    f === True, {},
    f === False, {{}},
    Head[f] === And, Join @@ (convert /@ (List @@ f)),
    Head[f] === Or, Fold[disjoin, {{}}, convert /@ (List @@ f)],
    MemberQ[{Less, Greater}, Head[f]], Module[{terms = List @@ f, q},
      Join @@ Table[
        q = Expand[If[Head[f] === Greater,
          terms[[k]] - terms[[k + 1]], terms[[k + 1]] - terms[[k]]]];
        If[! RationalPolynomialQ[q, v], Throw[InvalidInput[
          "Inequalities must be polynomials with exact rational coefficients in the declared variables."], tag]];
        AppendTo[polynomials, q]; {{{Length[polynomials], 1}}},
        {k, Length[terms] - 1}]],
    True, Throw[InvalidInput[
      "Use strict < or > polynomial inequalities combined with And or Or. Equality, non-strict inequalities and negated constraints are unsupported."], tag]
  ];
  clauses = Catch[convert[formula], tag];
  If[AssociationQ[clauses], clauses, <|"polynomials" -> polynomials, "clauses" -> clauses|>]
];

SolveFormula[formula_, v_List, tool_String, overrides_, seconds_] := (
  If[! ValidTimeQ[seconds], Return[InvalidInput["TimeLimit must be a positive number or Infinity."]]];
  WithinTime[seconds, Function[Null, Module[{encoded},
    If[! VariablesQ[v], Return[InvalidInput["Variables must be distinct, unassigned symbols."]]];
    encoded = EncodeFormula[formula, v];
    If[KeyExistsQ[encoded, "status"], Return[encoded]];
    SolveEncoded[encoded["polynomials"], encoded["clauses"], v, tool, overrides,
      If[tool === "2D-LS", seconds, Infinity]]]]]
);
End[];
EndPackage[];
