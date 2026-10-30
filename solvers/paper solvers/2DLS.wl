(* 2D-LS: local search for strict polynomial inequalities. *)
If[! MemberQ[$Packages, "TwoDLSCore`"],
  Get[FileNameJoin[{DirectoryName[DirectoryName[DirectoryName[$InputFileName]]], "components", "TwoDLSCore.wl"}]]];
If[! MemberQ[$Packages, "HELMSSolverAPI`"],
  Get[FileNameJoin[{DirectoryName[DirectoryName[DirectoryName[$InputFileName]]], "components", "SolverAPI.wl"}]]];
TwoDLS`Solve::usage = "Solve[formula, variables] searches for an exact model of a strict polynomial formula. Solve[polynomials, pairCNF, variables] accepts pair-CNF, where {i,s} means s*polynomials[[i]]>0. Returns SAT with an exact assignment when found; UNKNOWN does not establish unsatisfiability. Options: \"Config\" -> <||>, \"TimeLimit\" -> Infinity.";
Options[TwoDLS`Solve] = {"Config" -> <||>, "TimeLimit" -> Infinity};
TwoDLS`Solve[p_List, c_List, v_List, OptionsPattern[]] :=
  HELMSSolverAPI`SolveEncoded[p, c, v, "2D-LS", OptionValue["Config"], OptionValue["TimeLimit"]];
TwoDLS`Solve[formula_, v_List, OptionsPattern[]] :=
  HELMSSolverAPI`SolveFormula[formula, v, "2D-LS", OptionValue["Config"], OptionValue["TimeLimit"]];
TwoDLS`Solve[___] := <|"status" -> "error", "stage" -> "input",
  "reason" -> "Use TwoDLS`Solve[formula, variables] or TwoDLS`Solve[polynomials, pairCNF, variables]."|>;
