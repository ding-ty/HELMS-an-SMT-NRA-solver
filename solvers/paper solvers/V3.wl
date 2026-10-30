(* V3: the corresponding HELMS comparison strategy. *)
If[! MemberQ[$Packages, "PaperSolvers`"],
  Get[FileNameJoin[{DirectoryName[DirectoryName[DirectoryName[$InputFileName]]], "components", "SolverCore.wl"}]]];
If[! MemberQ[$Packages, "HELMSSolverAPI`"],
  Get[FileNameJoin[{DirectoryName[DirectoryName[DirectoryName[$InputFileName]]], "components", "SolverAPI.wl"}]]];
V3`Solve::usage = "Solve[formula, variables] accepts strict polynomial inequalities combined with And and Or. Solve[polynomials, pairCNF, variables] accepts indexed CNF, where {i,s} means s*polynomials[[i]]>0. Returns an association. Options: \"Config\" -> <||>, \"TimeLimit\" -> Infinity.";
Options[V3`Solve] = {"Config" -> <||>, "TimeLimit" -> Infinity};
V3`Solve[p_List, c_List, v_List, OptionsPattern[]] :=
  HELMSSolverAPI`SolveEncoded[p, c, v, "V3", OptionValue["Config"], OptionValue["TimeLimit"]];
V3`Solve[formula_, v_List, OptionsPattern[]] :=
  HELMSSolverAPI`SolveFormula[formula, v, "V3", OptionValue["Config"], OptionValue["TimeLimit"]];
V3`Solve[___] := <|"status" -> "error", "stage" -> "input",
  "reason" -> "Use V3`Solve[formula, variables] or V3`Solve[polynomials, pairCNF, variables]."|>;
