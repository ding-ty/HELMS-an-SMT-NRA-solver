(* The source-derived Wolfram Language LS baseline. *)
If[! MemberQ[$Packages, "PaperSolvers`"],
  Get[FileNameJoin[{DirectoryName[DirectoryName[DirectoryName[$InputFileName]]], "components", "SolverCore.wl"}]]];
If[! MemberQ[$Packages, "HELMSSolverAPI`"],
  Get[FileNameJoin[{DirectoryName[DirectoryName[DirectoryName[$InputFileName]]], "components", "SolverAPI.wl"}]]];
If[! MemberQ[$Packages, "PaperWolframLS`"],
  Get[FileNameJoin[{DirectoryName[DirectoryName[DirectoryName[$InputFileName]]], "components", "WolframLSCore.wl"}]]];
LSwolfram`Solve::usage = "Solve[formula, variables] accepts strict polynomial inequalities combined with And and Or. Solve[polynomials, pairCNF, variables] accepts indexed CNF, where {i,s} means s*polynomials[[i]]>0. Returns an association. Options: \"Config\" -> <||>, \"TimeLimit\" -> Infinity.";
Options[LSwolfram`Solve] = {"Config" -> <||>, "TimeLimit" -> Infinity};
LSwolfram`Solve[p_List, c_List, v_List, OptionsPattern[]] :=
  HELMSSolverAPI`SolveEncoded[p, c, v, "LS-WL", OptionValue["Config"], OptionValue["TimeLimit"]];
LSwolfram`Solve[formula_, v_List, OptionsPattern[]] :=
  HELMSSolverAPI`SolveFormula[formula, v, "LS-WL", OptionValue["Config"], OptionValue["TimeLimit"]];
LSwolfram`Solve[___] := <|"status" -> "error", "stage" -> "input",
  "reason" -> "Use LSwolfram`Solve[formula, variables] or LSwolfram`Solve[polynomials, pairCNF, variables]."|>;
