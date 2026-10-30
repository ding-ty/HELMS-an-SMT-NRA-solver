(* Comparative strategies used in the paper. *)
If[! MemberQ[$Packages, "PaperSolvers`"],
  Get[FileNameJoin[{DirectoryName[$InputFileName], "SolverCore.wl"}]]];
If[! MemberQ[$Packages, "HELMSSolverAPI`"],
  Get[FileNameJoin[{DirectoryName[$InputFileName], "SolverAPI.wl"}]]];
PaperAblations`Solve::usage = "Solve[polynomials, pairCNF, variables, solver, config] runs V1-V5 or LS-WL for comparison.";
PaperAblations`Solve[p_List, c_List, v_List, solver_String, cfg_Association] :=
  If[MemberQ[{"V1", "V2", "V3", "V4", "V5", "LS-WL"}, solver],
    HELMSSolverAPI`SolveEncoded[p, c, v, solver, cfg, Infinity],
    <|"status" -> "error", "reason" -> "unknown comparison solver"|>];
