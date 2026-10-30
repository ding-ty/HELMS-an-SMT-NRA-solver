(* V4: the corresponding HELMS comparison strategy. *)
If[! MemberQ[$Packages, "PaperSolvers`"],
  Get[FileNameJoin[{DirectoryName[DirectoryName[DirectoryName[$InputFileName]]], "components", "SolverCore.wl"}]]];
If[! MemberQ[$Packages, "HELMSSolverAPI`"],
  Get[FileNameJoin[{DirectoryName[DirectoryName[DirectoryName[$InputFileName]]], "components", "SolverAPI.wl"}]]];
V4`Solve::usage = "Solve[formula, variables] accepts strict polynomial inequalities combined with And and Or. Solve[polynomials, pairCNF, variables] accepts indexed CNF, where {i,s} means s*polynomials[[i]]>0. Returns an association. Options: \"Config\" -> <||>, \"TimeLimit\" -> Infinity.";
Options[V4`Solve] = {"Config" -> <||>, "TimeLimit" -> Infinity};
V4`Solve[p_List, c_List, v_List, OptionsPattern[]] :=
  HELMSSolverAPI`SolveEncoded[p, c, v, "V4", OptionValue["Config"], OptionValue["TimeLimit"]];
V4`Solve[formula_, v_List, OptionsPattern[]] :=
  HELMSSolverAPI`SolveFormula[formula, v, "V4", OptionValue["Config"], OptionValue["TimeLimit"]];
V4`Solve[___] := <|"status" -> "error", "stage" -> "input",
  "reason" -> "Use V4`Solve[formula, variables] or V4`Solve[polynomials, pairCNF, variables]."|>;
