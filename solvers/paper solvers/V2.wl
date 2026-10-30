(* V2: the corresponding HELMS comparison strategy. *)
If[! MemberQ[$Packages, "PaperSolvers`"],
  Get[FileNameJoin[{DirectoryName[DirectoryName[DirectoryName[$InputFileName]]], "components", "SolverCore.wl"}]]];
If[! MemberQ[$Packages, "HELMSSolverAPI`"],
  Get[FileNameJoin[{DirectoryName[DirectoryName[DirectoryName[$InputFileName]]], "components", "SolverAPI.wl"}]]];
V2`Solve::usage = "Solve[formula, variables] accepts strict polynomial inequalities combined with And and Or. Solve[polynomials, pairCNF, variables] accepts indexed CNF, where {i,s} means s*polynomials[[i]]>0. Returns an association. Options: \"Config\" -> <||>, \"TimeLimit\" -> Infinity.";
Options[V2`Solve] = {"Config" -> <||>, "TimeLimit" -> Infinity};
V2`Solve[p_List, c_List, v_List, OptionsPattern[]] :=
  HELMSSolverAPI`SolveEncoded[p, c, v, "V2", OptionValue["Config"], OptionValue["TimeLimit"]];
V2`Solve[formula_, v_List, OptionsPattern[]] :=
  HELMSSolverAPI`SolveFormula[formula, v, "V2", OptionValue["Config"], OptionValue["TimeLimit"]];
V2`Solve[___] := <|"status" -> "error", "stage" -> "input",
  "reason" -> "Use V2`Solve[formula, variables] or V2`Solve[polynomials, pairCNF, variables]."|>;
