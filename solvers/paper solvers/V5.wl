(* V5: the corresponding HELMS comparison strategy. *)
If[! MemberQ[$Packages, "PaperSolvers`"],
  Get[FileNameJoin[{DirectoryName[DirectoryName[DirectoryName[$InputFileName]]], "components", "SolverCore.wl"}]]];
If[! MemberQ[$Packages, "HELMSSolverAPI`"],
  Get[FileNameJoin[{DirectoryName[DirectoryName[DirectoryName[$InputFileName]]], "components", "SolverAPI.wl"}]]];
V5`Solve::usage = "Solve[formula, variables] accepts strict polynomial inequalities combined with And and Or. Solve[polynomials, pairCNF, variables] accepts indexed CNF, where {i,s} means s*polynomials[[i]]>0. Returns an association. Options: \"Config\" -> <||>, \"TimeLimit\" -> Infinity.";
Options[V5`Solve] = {"Config" -> <||>, "TimeLimit" -> Infinity};
V5`Solve[p_List, c_List, v_List, OptionsPattern[]] :=
  HELMSSolverAPI`SolveEncoded[p, c, v, "V5", OptionValue["Config"], OptionValue["TimeLimit"]];
V5`Solve[formula_, v_List, OptionsPattern[]] :=
  HELMSSolverAPI`SolveFormula[formula, v, "V5", OptionValue["Config"], OptionValue["TimeLimit"]];
V5`Solve[___] := <|"status" -> "error", "stage" -> "input",
  "reason" -> "Use V5`Solve[formula, variables] or V5`Solve[polynomials, pairCNF, variables]."|>;
