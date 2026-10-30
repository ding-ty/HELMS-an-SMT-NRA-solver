(* Compatibility loader for standalone 2D-LS support operations. *)
If[! MemberQ[$Packages, "TwoDLSCore`"],
  Get[FileNameJoin[{DirectoryName[$InputFileName], "TwoDLSCore.wl"}]]];
