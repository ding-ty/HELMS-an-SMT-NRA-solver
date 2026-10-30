(* V1: the corresponding HELMS comparison strategy. *)
If[! MemberQ[$Packages, "PaperSolvers`"],
  Get[FileNameJoin[{DirectoryName[DirectoryName[DirectoryName[$InputFileName]]], "components", "SolverCore.wl"}]]];
If[! MemberQ[$Packages, "HELMSSolverAPI`"],
  Get[FileNameJoin[{DirectoryName[DirectoryName[DirectoryName[$InputFileName]]], "components", "SolverAPI.wl"}]]];
V1`Solve::usage = "Solve[formula, variables] accepts strict polynomial inequalities combined with And and Or. Solve[polynomials, pairCNF, variables] accepts indexed CNF, where {i,s} means s*polynomials[[i]]>0. Returns an association. Options: \"Config\" -> <||>, \"TimeLimit\" -> Infinity.";
Options[V1`Solve] = {"Config" -> <||>, "TimeLimit" -> Infinity};
V1`Solve[p_List, c_List, v_List, OptionsPattern[]] :=
  HELMSSolverAPI`SolveEncoded[p, c, v, "V1", OptionValue["Config"], OptionValue["TimeLimit"]];
V1`Solve[formula_, v_List, OptionsPattern[]] :=
  HELMSSolverAPI`SolveFormula[formula, v, "V1", OptionValue["Config"], OptionValue["TimeLimit"]];
V1`Solve[___] := <|"status" -> "error", "stage" -> "input",
  "reason" -> "Use V1`Solve[formula, variables] or V1`Solve[polynomials, pairCNF, variables]."|>;
