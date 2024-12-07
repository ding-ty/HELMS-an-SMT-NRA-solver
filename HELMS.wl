(* ::Package:: *)

BeginPackage["lsmcsat`"];


GetSampleInterval::usage="GetSampleInterval";


Ps::usage="Ps";


Pr::usage="Pr";


Pc::usage="Pc";


Pos::usage="Return open sample cad projection of A.";


Pmc::usage="Return McCallum projection of A.";


polytosmt2::usage="polytosmt2";


ClauseResolve::usage="ClauseResolve";


CheckConflictHalf::usage="half conflict set check.";


Leadcoeff::usage="Leadcoeff";


FindMid::usage="findmid.";


MCSATSolver::usage="MCSAT solver.";


SatCheck::usage="check if cnf is sat.";


SearchAndApplyOp1::usage="search the operation(celljump along axis) by real root isolation with the highest score and apply it.";


SearchAndApplyOp2::usage="search the operation(celljump along axis) by MCSAT with the highest score and apply it.";


MaxScoreOp1::usage="apply the operation(celljump along axis) by real root isolation with the highest score where cjump(xi,l), l in fal_cl or l in sat_l.";


MaxScoreOp2::usage="apply the operation(celljump along axis) by MCSAT with the highest score where cjump(xi,l), l in fal_cl or l in sat_l.";


SamplePoint::usage="get sample points of real root isolation.";


UpdateWeight::usage="update clause weight.";


GetAtomInFalseClause::usage="all atoms in false clauses in cnf.";


GetFalseAtomInTrueClause::usage="false atoms in true clauses in cnf.";


GradSearchAndApplyOp1::usage="search the operation(celljump along some directions) by real root isolation with the highest score and apply it.";


GradSearchAndApplyOp2::usage="search the operation(celljump along some directions) by MCSAT with the highest score and apply it.";


GradMaxScoreOp1::usage="apply the operation(celljump along some directions) by real root isolation with the highest score where cjump(xi,l), l in fal_cl or l in sat_l.";


GradMaxScoreOp2::usage="apply the operation(celljump along some directions) by MCSAT with the highest score where cjump(xi,l), l in fal_cl or l in sat_l.";


LS::usage="one restart of local search.";


LSSolver::usage="local search solver.";


ELS::usage="one restart of extended local search.";


ELSSolver::usage="extended local search solver.";


Preproc::usage="preprocessing input formula.";


Solver::usage="cooperation of mcsat and local search.";


SMT::usage="input form is an ineqs SMT formula.";


Begin["`Private`"];


polytosmt2[f_]:=
Module[{a=Head[f],l,h,i},
    If[SameQ[a, Power],
        l={"(*"};
        h=" "<>polytosmt2[f[[1]]];
        For[i=1,i<=f[[2]],++i,AppendTo[l,h]];
        Return[StringJoin[Append[l,")"]]]
    ];
    If[SameQ[a,Plus],h="(+",
        If[SameQ[a,Times],h="(*",
            If[f<0,Return["(- "<>ToString[-f,InputForm]<>")"],
                Return[ToString[f,InputForm]],
                Return[ToString[f,InputForm]]
            ]
        ]
    ];
    l=Map[" "<>polytosmt2[#]&,f];
    l[[0]]=List;
    Return[StringJoin[{h,l,")"}]];
];


Pc[A_,x_]:=Flatten[CoefficientList[A,x]];


Pc[A_List,M_Association ,x_]:=
Module[{p1={},p2={},c,i,j},
    For[i=1,i<=Length[A],++i,
        c=CoefficientList[A[[i]],x];
        For[j=Length[c],j>0,--j,
            AppendTo[p1,c[[j]]];
            If[UnsameQ[c[[j]]/.M,0],Break[]];        
        ];
        If[SameQ[p1[[-1]]/.M,0],AppendTo[p2,A[[i]]]];            
    ];
    Return[{p1,p2}];
];


Pr[A_List,x_]:=Map[Apply[Resultant[#1,#2,x]&],Subsets[A,{2}]];


Pr[A_List,B_List,x_]:=Map[Apply[Resultant[#1,#2,x]&],Select[Tuples[{A,B}],UnsameQ[#[[1]],#[[2]]]&]];


Pmc[A_List,M_Association,x_]:=
Module[{A1,B,M1=KeyDrop[M,x],p1},
    A1=DeleteDuplicates[Flatten[Map[FactorList,A][[All,All,1]]]];
    B=Select[A1,Not[MemberQ[Variables[#],x]]&];
    A1=Select[A1,MemberQ[Variables[#],x]&];
    p1=Pc[A1,M1,x][[1]];
    A1=Select[A1,MemberQ[Variables[#/.M1],x]&];
    Return[DeleteDuplicates[Flatten[{B,p1,Discriminant[A1,x],Pr[A1,x]}]]];
];


Pmc[A_List,x_]:=
Module[{A1,B},
    A1=DeleteDuplicates[Flatten[Map[FactorList,A][[All,All,1]]]];
    B=Select[A1,Not[MemberQ[Variables[#],x]]&];
    A1=Select[A1,MemberQ[Variables[#],x]&];
    Return[DeleteDuplicates[Flatten[{B,Pc[A1,x],Discriminant[A1,x],Pr[A1,x]}]]];
];


GetSampleInterval[A_List,M_Association,x_]:=
Module[{A1=DeleteDuplicates[Flatten[Map[FactorList,A][[All,All,1]]]],B,A0,A2,x0=M[x],
        M1=KeyDrop[M,x],rootintervals,numroot,tmpindex,
        rightindex,rightrootindex,leftindex,leftrootindex},
    B=Select[A1,(Not[MemberQ[Variables[#],x]] && UnsameQ[Variables[#],{}])&];
    A1=Select[A1,MemberQ[Variables[#],x]&];
    A0=Select[A1,MemberQ[Variables[#/.M1],x]&];
    If[Length[A0]==0,Return[{{},{B,A1,A0,{{},{}}}}]];
    rootintervals=RootIntervals[A0/.M1];
    numroot=Length[rootintervals[[1]]];
    If[numroot==0,Return[{{},{B,A1,A0,{{},{}}}}]];
    A2=A0[[DeleteDuplicates[Flatten[rootintervals[[2]]]]]];
    tmpindex=Max[LengthWhile[rootintervals[[1]],(x0>#[[1]]|| #[[2]]==x0 )&],1];
    (*Print[rootintervals,M[x]];
    Print[tmpindex,rootintervals[[1,tmpindex]]];*)
    rightindex=rootintervals[[2,tmpindex,1]];
    rightrootindex=Plus@@Map[Count[#,rightindex]&,rootintervals[[2,;;tmpindex]]];
    If[SameQ[A0[[rightindex]]/.M,0],
        Return[{{{Equal,A0[[rightindex]],rightrootindex}},{B,A1,A0,{A2,{A0[[rightindex]]}}}}]];
    If[x0>=rootintervals[[1,tmpindex,2]] ||  x0>Root[A0[[rightindex]]/.M1,rightrootindex],
        leftindex=rightindex;
        leftrootindex=rightrootindex;
        If[tmpindex==numroot,
            Return[{{{Greater,A0[[leftindex]],leftrootindex}},{B,A1,A0,{A2,{A0[[leftindex]]}}}}]];
        rightindex=rootintervals[[2,tmpindex+1,1]];
        rightrootindex=Plus@@Map[Count[#,rightindex]&,rootintervals[[2,1;;tmpindex+1]]];
        ,
        If[tmpindex==1,
            Return[{{{Less,A0[[rightindex]],rightrootindex}},{B,A1,A0,{A2,{A0[[rightindex]]}}}}]];
        leftindex=rootintervals[[2,tmpindex-1,1]];
        leftrootindex=Plus@@Map[Count[#,leftindex]&,rootintervals[[2,1;;tmpindex-1]]];

    ];
    If[rightindex==leftindex,
        Return[{{{Greater,A0[[leftindex]],leftrootindex},
            {Less,A0[[rightindex]],rightrootindex}},{B,A1,A0,{A2,{A0[[leftindex]]}}}}],
        Return[{{{Greater,A0[[leftindex]],leftrootindex},
            {Less,A0[[rightindex]],rightrootindex}},{B,A1,A0,{A2,{A0[[leftindex]],A0[[rightindex]]}}}}]]
];


Ps[l_List,M_Association,x_]:=Module[{p1,p2,p3,M1=KeyDrop[M,x]},
    p1=Pc[l[[2]],M1,x];
    (*If[Length[p1[[2]]]!=0,Print[p1[[2]],M,x]];*)
    p2=Discriminant[l[[3]],x];
    p3=Pr[l[[4,1]],l[[4,2]],x];
    Return[DeleteDuplicates[{Sequence@@l[[1]],Sequence@@p1[[1]],Sequence@@p2,Sequence@@p3}]];
];


Pos[A_List,M_Association,x_,mod_:"Root"]:=
Module[{i,A1,B,M1,p1,p2,p3,A0,A2,x0,rootintervals,numroot,tmpindex,tmprootindex,rightindex,rightrootindex,leftindex,leftrootindex},
    Assert[mod=="Root" || mod=="poly"];
    A1=DeleteDuplicates[Flatten[Map[FactorList,A][[All,All,1]]]];
    B=Select[A1,Not[MemberQ[Variables[#],x]]&];
    A1=Select[A1,MemberQ[Variables[#],x]&];
    M1=KeyDrop[M,x];
    p1=Pc[A1,M1,x][[1]];
    p2=Discriminant[A1,x];
    A0=Select[A1,MemberQ[Variables[#/.M1],x]&];
    If[Length[A0]==0,Return[{DeleteDuplicates[Flatten[{B,p1,p2}]],x}]];
    rootintervals=RootIntervals[A0/.M1];
    numroot=Length[rootintervals[[1]]];
    If[numroot==0,
        If[SameQ[mod,"Root"],Return[{DeleteDuplicates[Flatten[{B,p1,p2}]],True}]];
        If[SameQ[mod,"Poly"],Return[{DeleteDuplicates[Flatten[{B,p1,p2}]],{}}]];
    ];
    A2=A0[[DeleteDuplicates[Flatten[rootintervals[[2]]]]]];
    tmpindex=FirstPosition[A0/.M,0,{0},1][[1]];
    If[tmpindex!=0,
        tmprootindex=0;
        For[i=1,i<=numroot && (M[x]>rootintervals[[1,i,1]] || M[x]>=rootintervals[[1,i,2]]),++i,
            tmprootindex+=Count[rootintervals[[2,i]],tmpindex]];
        If[Length[A2]>1,p3=Pr[A2,{A0[[tmpindex]]},x],p3={}];
        If[SameQ[mod,"Root"],Return[{DeleteDuplicates[Flatten[{B,p1,p2,p3}]],
                               x==Root[A0[[tmpindex]]/.x->#&,tmprootindex]}]];
        If[SameQ[mod,"Poly"],Return[{DeleteDuplicates[Flatten[{B,p1,p2,p3}]],
                               {{Equal,A0[[tmpindex]],tmprootindex}}}]];
    ];
    (*Print[rootintervals];*)    
    tmpindex=Max[LengthWhile[rootintervals[[1]],M[x]>#[[1]]&],1];
    (*Print[tmpindex];*)    
    rightindex=rootintervals[[2,tmpindex,1]];
    rightrootindex=Plus@@Map[Count[#,rightindex]&,rootintervals[[2,1;;tmpindex]]];
    x0=Root[A0[[rightindex]]/.M1,rightrootindex];
    If[M[x]<x0,
        (*Print["<"];*)
        If[tmpindex==1,
            p3=Pr[A2,{A0[[rightindex]]},x];
            If[SameQ[mod,"Root"],Return[{DeleteDuplicates[Flatten[{B,p1,p2,p3}]],
                x<Root[A0[[rightindex]]/.(x->#)&,rightrootindex]}]];
            If[SameQ[mod,"Poly"],Return[{DeleteDuplicates[Flatten[{B,p1,p2,p3}]],
                {{Less,A0[[rightindex]],rightrootindex}}}]];
            
        ];
        leftindex=rootintervals[[2,tmpindex-1,1]];
        leftrootindex=Plus@@Map[Count[#,leftindex]&,rootintervals[[2,1;;tmpindex-1]]];
        ,
        (*Print[">"];*)
        leftindex=rightindex;
        leftrootindex=rightrootindex;
        If[tmpindex==numroot,
            p3=Pr[A2,{A0[[leftindex]]},x];
            If[SameQ[mod,"Root"],Return[{DeleteDuplicates[Flatten[{B,p1,p2,p3}]],
                Root[A0[[leftindex]]/.(x->#)&,leftrootindex]<x}]];
            If[SameQ[mod,"Poly"],Return[{DeleteDuplicates[Flatten[{B,p1,p2,p3}]],
                {{Greater,A0[[leftindex]],leftrootindex}}}]];
        ];
        rightindex=rootintervals[[2,tmpindex+1,1]];
        rightrootindex=Plus@@Map[Count[#,rightindex]&,rootintervals[[2,1;;tmpindex+1]]];
    ];
    If[rightindex==leftindex,
        p3=Pr[A2,{A0[[leftindex]]},x],
        p3=Pr[A2,{A0[[rightindex]],A0[[leftindex]]},x]];
    If[SameQ[mod,"Root"],Return[{DeleteDuplicates[Flatten[{B,p1,p2,p3}]],
       Root[A0[[leftindex]]/.(x->#)&,leftrootindex]<x<Root[A0[[rightindex]]/.(x->#)&,rightrootindex]}]];
    If[SameQ[mod,"Poly"],Return[{DeleteDuplicates[Flatten[{B,p1,p2,p3}]],
       {{Greater,A0[[leftindex]],leftrootindex},
        {Less,A0[[rightindex]],rightrootindex}}}]];
];


ClauseResolve[Clause_,E_,F_]:=Union[Clause,E]/.{F->Nothing,(-F)->Nothing};


Leadcoeff[F_,x_]:=Last[CoefficientList[F,x]];


CheckConflictHalf[conflictstatelist_List,f1_,x_,l_Integer,isgreat_,isequal_]:=
Module[{isclose,rootnum,a,b,k,midcheck,skip,selectstate,status=False,rootindex,newconflictstatelist={},listindex,listlength},
    isclose=!isequal;
    If[SameQ[f1,0],
        If[isclose,Return[{False,{{-Infinity,Infinity,False,l}}}],Return[{True,conflictstatelist}]]
    ];
    rootnum=CountRoots[f1,x];
    If[SameQ[rootnum, 0],
        If[Not[Xor[Leadcoeff[f1,x]>0,isgreat]],
            Return[{True,conflictstatelist}],Return[{False,{{-Infinity,Infinity,False,l}}}]
        ]
    ];
    If[Not[Xor[Leadcoeff[f1,x]>0 && Mod[rootnum,2]==0 || Leadcoeff[f1,x]<0 && Mod[rootnum,2]==1 ,isgreat]],
        a=Root[f1,1];
        rootindex=2;
        If[rootindex>rootnum,b=Infinity,b=Root[f1,rootindex]];
        ,
        a=-Infinity;b=Root[f1,1];
        rootindex=1;
    ];
    skip=NestWhile[(If[#<rootnum,a=Root[f1,#+1];If[#+2>rootnum,b=Infinity,b=Root[f1,#+1]]];#+2)&,
            #, #<=rootnum+1 && a==b&]&;
    If[!isclose, rootindex=skip[rootindex]];
    listindex=1;
    listlength=Length[conflictstatelist];
    midcheck=(status || (Length[newconflictstatelist]>0 && 
                    (#1>newconflictstatelist[[-1,2]] || 
                        #1==newconflictstatelist[[-1,2]] && !#2 && !newconflictstatelist[[-1,3]]) ||
                    Length[newconflictstatelist]==0 && #1!=-Infinity
                ))&;
    While[listindex<=listlength && rootindex<rootnum+2 ,
        If[a<conflictstatelist[[listindex,1]] ||
            (a==conflictstatelist[[listindex,1]] &&  
                ((a!=-Infinity && isclose && !conflictstatelist[[listindex,3]]) ||
                 ((a==-Infinity || isclose|| !conflictstatelist[[listindex,3]]) &&
                    (b>conflictstatelist[[listindex,2]] ||
                        (b==conflictstatelist[[listindex,2]] && 
                            (isclose|| !conflictstatelist[[listindex,3]]|| b==Infinity)
                        )
                    )
                 )
                )
            ),
            status=midcheck[a,isclose];
            AppendTo[newconflictstatelist,{a,b,isclose,l}];
            If[b==Infinity,
                Return[{status,newconflictstatelist}];
            ];
            listindex=NestWhile[#+1&,listindex,
                #<=listlength && 
                    (b>conflictstatelist[[#,2]] || 
                     (isclose || !conflictstatelist[[#,3]]) && b==conflictstatelist[[#,2]])&
            ];
            ++rootindex;++rootindex;
            If[rootindex>rootnum+1 ,Break[]];
            a=Root[f1,rootindex-1];
            If[rootindex>rootnum,b=Infinity,b=Root[f1,rootindex]];
            If[!isclose, rootindex=skip[rootindex]];
            , 
            status=midcheck[conflictstatelist[[listindex,1]],conflictstatelist[[listindex,3]]];
            AppendTo[newconflictstatelist,conflictstatelist[[listindex]]];
            If[conflictstatelist[[listindex,2]]==Infinity,
                Return[{status,newconflictstatelist}];
            ];
            k=rootindex;
            rootindex=NestWhile[(If[#+2>rootnum,b=Infinity,b=Root[f1,#+1]];#+2)&,rootindex,
                #<=rootnum+1 && (
                    newconflictstatelist[[-1,2]]>b ||
                    (!isclose || newconflictstatelist[[-1,3]]) && b==newconflictstatelist[[-1,2]] )&
            ];
            ++listindex;
            If[rootindex>rootnum+1,Break[]];
            If[rootindex>k,a=Root[f1,rootindex-1]];
            If[isclose,rootindex=
                NestWhile[(If[#<rootnum,a=Root[f1,#+1];If[#+2>rootnum,b=Infinity,b=Root[f1,#+1]]];#+2)&,
                  rootindex, #<=rootnum+1 && b<=newconflictstatelist[[-1,2]]&]];
            If[!isclose, rootindex=skip[rootindex]];
        ]
    ];
    If[listindex<=listlength,
        status=midcheck[conflictstatelist[[listindex,1]],conflictstatelist[[listindex,3]]];
        Scan[(status=midcheck[#[[1]],#[[3]]];AppendTo[newconflictstatelist,#])&,
            conflictstatelist[[listindex;;]]]
    ];
    If[rootindex<rootnum+2,
        status=midcheck[a,isclose];
        AppendTo[newconflictstatelist,{a,b,isclose,l}];
        Scan[(a=Root[f1,#];b=If[#>=rootnum,Infinity,Root[f1,#+1]];
                If[isclose  && b>newconflictstatelist[[-1,2]] || a!=b,
                    status=midcheck[a,isclose];
                    AppendTo[newconflictstatelist,{a,b,isclose,l}]])&,
                        Range[rootindex+1,rootnum,2]]
    ];
    If[!status && newconflictstatelist[[-1,2]]!=Infinity,status=True];
    Return[{status,newconflictstatelist}]
];


CheckConflictHalf[conflictstatelist_List,r_,l_Integer,isgreat_,isequal_]:=
Module[{isclose,status=False,index,newlist},
    isclose=!isequal;
    If[!isgreat,
        If[r==-Infinity,Return[{False,{{-Infinity,Infinity,isclose,l}}}]];
        newlist=TakeWhile[conflictstatelist,
            (#[[1]]<r || !isclose && #[[3]] && #[[1]]==r)&];
        If[Length[newlist]==0 || newlist[[-1,2]]!=Infinity, 
            AppendTo[newlist,{r,Infinity,isclose,l}]];
        
    ,
        If[r==Infinity,Return[{False,{{-Infinity,Infinity,isclose,l}}}]];
        index=LengthWhile[conflictstatelist,
            (#[[2]]<r || (isclose || !#[[3]]) && #[[2]]==r)&];
        newlist=conflictstatelist[[index+1;;]];
        If[Length[newlist]==0 || newlist[[1,1]]!=-Infinity,
            newlist={{-Infinity,r,isclose,l},Sequence@@newlist}];
    ];
    If[newlist[[1,1]]!=-Infinity || newlist[[-1,2]]!=Infinity,Return[{True,newlist}]];
    Scan[
           (If[newlist[[#-1,2]]<newlist[[#,1]] || 
                !newlist[[#,3]] && !newlist[[#-1,3]] && newlist[[#-1,2]]==newlist[[#,1]],
                status=True;Return[]])&,Range[2,Length[newlist]]];
    Return[{status,newlist}];
];


FindMid[x_,y_]:=Module[{x1=1,y1=0},
    NestWhile[(x1=IsolatingInterval[x,#][[2]];y1=IsolatingInterval[y,#][[1]];#/10)&,1,x1>=y1&]; 
    (* x1=IsolatingInterval[x,(y-x)/2][[2]];y1=IsolatingInterval[y,(y-x)/2][[1]]; *)
    Return[(y1+x1)/2];
]


FindMid[conflictstatelist_List]:=Module[{len=0,mid=Infinity,x},
    len=Length[conflictstatelist];
    If[len==0,Return[1]];
    If[conflictstatelist[[1,1]]!=-Infinity,
        (* Return[FindInstance[x < conflictstatelist[[1,1]] , {x}, Rationals][[1,1,2]]] *)
        x=IsolatingInterval[conflictstatelist[[1,1]]];
        Return[If[x[[1]]<x[[2]],x[[1]],x[[1]]-1/10]];
    ];
    If[conflictstatelist[[-1,2]]!=Infinity,
        (* Return[FindInstance[x > conflictstatelist[[-1,2]] , {x}, Rationals][[1,1,2]]] *)
       x=IsolatingInterval[conflictstatelist[[-1,2]]];
        Return[If[x[[1]]>x[[2]],x[[2]],x[[2]]+1/10]];
    ];
    Scan[If[conflictstatelist[[#-1,2]]<conflictstatelist[[#,1]],
            mid=FindMid[conflictstatelist[[#-1,2]],conflictstatelist[[#,1]]];
            (* mid=FindInstance[x> conflictstatelist[[#-1,2]] && x < conflictstatelist[[#,1]] , 
                 {x}, Rationals][[1,1,2]]; *)
            Return[],
            If[mid==Infinity && conflictstatelist[[#-1,2]]==conflictstatelist[[#,1]] && 
                !conflictstatelist[[#-1,3]] && !conflictstatelist[[#,3]],
                mid=conflictstatelist[[#-1,2]]]]&,
     Range[2,len]];
    Return[mid];
]


SatCheck[polyList_, cnf_, varList_, x_]:=
Module[{temp, polyValue, atomValue, clauseValue, cnfValue},
	polyValue = polyList/.x;
	atomValue = Function[{polyValue0, atom0}, Switch[atom0[[2]], 
	-1, polyValue[[atom0[[1]]]]<0,
	0, polyValue[[atom0[[1]]]]==0,
	1, polyValue[[atom0[[1]]]]>0
	]];
	clauseValue = Function[{polyValue0, clause0}, Or @@ Map[atomValue[polyValue0, #]&, clause0]];
	cnfValue = Function[{polyValue0, cnf0}, And @@ Map[clauseValue[polyValue0, #]&, cnf0]];
	Return[cnfValue[polyValue, cnf]];
];


SearchAndApplyOp1[polyList_, cnf_, varList_, x_, w_]:=
Module[{atomInFalseClause, xNew, falseAtomInTrueClause},
	atomInFalseClause = GetAtomInFalseClause[polyList, cnf, varList, x]; 
    (*Print["atom in false clause: ",atomInFalseClause];*)
    Which[Length[atomInFalseClause] > 0, 
    xNew = MaxScoreOp1[polyList, cnf, varList, x, w, atomInFalseClause];
    (*Print["x (search atomInFalseClause): ", xNew]*),
    True, falseAtomInTrueClause = GetFalseAtomInTrueClause[polyList, cnf, varList, x];
    (*Print["false atom in true clause", falseAtomInTrueClause];*)
    xNew = MaxScoreOp1[polyList, cnf, varList, x, w, falseAtomInTrueClause];
    (*Print["x (search falseAtomInTrueClause): ", xNew]*);
    ];
    Return[{xNew != x, xNew}];
];


SearchAndApplyOp2[polyList_, cnf_, varList_, x_, w_]:=
Module[{atomInFalseClause, xNew, falseAtomInTrueClause},
	atomInFalseClause = GetAtomInFalseClause[polyList, cnf, varList, x]; 
    (*Print["atom in false clause: ",atomInFalseClause];*)
    Which[Length[atomInFalseClause] > 0, 
    xNew = MaxScoreOp2[polyList, cnf, varList, x, w, atomInFalseClause];
    (*Print["x (search atomInFalseClause): ", xNew]*),
    True, falseAtomInTrueClause = GetFalseAtomInTrueClause[polyList, cnf, varList, x];
    (*Print["false atom in true clause", falseAtomInTrueClause];*)
    xNew = MaxScoreOp2[polyList, cnf, varList, x, w, falseAtomInTrueClause];
    (*Print["x (search falseAtomInTrueClause): ", xNew]*);
    ];
    (*Return[{Or@@Table[xNew[[i]]!=x[Keys[xNew][[i]]],{i,Length[xNew]}], xNew}];*)
    Return[{xNew != x,xNew}];
];


pp = 1;


MaxScoreOp1[polyList_, cnf_, varList_, x_, w_, atomList_]:=
Module[{i, j, k, DistanceToTruth, DistanceToSatisfaction, Score, atomTruth, falseAtomList, isolation, tempx, distanceToX, xOld, xNew, maxScoreX, samplePoint, xVar}, 
	DistanceToTruth = Function[{atom0, x0}, 
	Which[Sign[(polyList[[atom0[[1]]]])/.x0] == Sign[atom0[[2]]], 0, 
	True, Abs[(polyList[[atom0[[1]]]])/.x0]+pp]];
	
	DistanceToSatisfaction = Function[{clause0, x0}, Min[Table[DistanceToTruth[clause0[[i]],x0],{i,Length[clause0]}]]];
	
	Score = Function[{cnf0, x0, x1}, 
	Sum[(DistanceToSatisfaction[cnf0[[i]], x0] - DistanceToSatisfaction[cnf0[[i]], x1])* w[cnf0[[i]]],{i,Length[cnf0]}]];
	
	
	atomTruth = Function[atom0, Sign[(polyList/.x)[[atom0[[1]]]]] == Sign[atom0[[2]]]];
	falseAtomList = Select[atomList, atomTruth[#] == False &];
	(*Print["false atom list: ", falseAtomList];*)
	i = 1; maxScoreX = x; xOld = x;
	While[i <= Length[varList],
		(*Print["\:5bf9",varList[[i]],"\:505a\:5b9e\:6839\:9694\:79bb"];*)
		tempx = x; tempx[varList[[i]]] = varList[[i]];
		(*Print["temp x: ", tempx];*)
		samplePoint = SamplePoint[polyList, falseAtomList, tempx]; (* \:5bf9\:7b2ci\:4e2a\:53d8\:91cf\:505a\:5b9e\:6839\:9694\:79bb\:ff0c\:5f97\:5230\:7684\:6837\:672c\:70b9*)
		(*Print["sample point: ",samplePoint]; *)
		j = 1;
		While[j <= Length[falseAtomList],
			Switch[falseAtomList[[j,2]],
			-1, (* \:7ea6\:675f\:4e3ap(x)<0, op\:4e3a\:6cbfxi\:8f74\:65b9\:5411\:8ddd\:79bb\:539f\:6765\:8d4b\:503c\:6700\:8fd1\:7684\:8d1f\:6837\:672c\:70b9 *)
			xVar = Select[samplePoint[falseAtomList[[j]]], ((polyList[[falseAtomList[[j,1]]]]/.tempx)/.{varList[[i]]->#}) < 0 &]; (* \:8d1f\:6837\:672c\:70b9 *)
			(*Print["\:8d1f\:6837\:672c\:70b9:",xVar]; *)
			Which[xVar != {},
			distanceToX = Table[Abs[xVar[[k]] - x[varList[[i]]]], {k, Length[xVar]}]; (* \:8d1f\:6837\:672c\:70b9\:5230\:539f\:6765\:8d4b\:503c\:7684\:8ddd\:79bb *)
			(*Print["distance to x: ",distanceToX];*)
			xNew =  x; 
			xNew[varList[[i]]] = xVar[[Position[distanceToX, Min[distanceToX]][[1,1]]]];
			(*Print["x new: ",xNew]; *)
			(*Print["Score: ",Score[cnf,xOld,xNew]]; *)
			Which[Score[cnf, xOld, xNew] > 0, maxScoreX = xNew; xOld = xNew;]\:ff1b
			(*Print["max score x: ", maxScoreX];*)
			],
			
			1, (* \:7ea6\:675f\:4e3ap(x)>0, op\:4e3a\:6cbfxi\:8f74\:65b9\:5411\:8ddd\:79bb\:539f\:6765\:8d4b\:503c\:6700\:8fd1\:7684\:6b63\:6837\:672c\:70b9 *)
			xVar = Select[samplePoint[falseAtomList[[j]]], ((polyList[[falseAtomList[[j,1]]]]/.tempx)/.{varList[[i]]->#}) > 0 &]; (* \:6b63\:6837\:672c\:70b9 *)
			Which[xVar != {},
			distanceToX = Table[Abs[xVar[[k]] - x[varList[[i]]]], {k, Length[xVar]}]; (* \:6b63\:6837\:672c\:70b9\:5230\:539f\:6765\:8d4b\:503c\:7684\:8ddd\:79bb *)
			xNew =  x; 
			xNew[varList[[i]]] = xVar[[Position[distanceToX, Min[distanceToX]][[1,1]]]];
			Which[Score[cnf, xOld, xNew] > 0, maxScoreX = xNew; xOld = xNew;];
			];
			];
			j++;
		];
		i++;
	];
	Return[maxScoreX];
];


MaxScoreOp2[polyList_, cnf_, varList_, x_, w_, atomList_]:=
Module[{i, j, k, DistanceToTruth, DistanceToSatisfaction, Score, atomTruth, falseAtomList, falseAtomNum, ansMCSAT, opList={}, tempx, xNew}, 
	DistanceToTruth = Function[{atom0, x0}, 
	Which[Sign[(polyList[[atom0[[1]]]])/.x0] == Sign[atom0[[2]]], 0, 
	True, Abs[(polyList[[atom0[[1]]]])/.x0]+pp]];
	
	DistanceToSatisfaction = Function[{clause0, x0}, Min[Table[DistanceToTruth[clause0[[i]],x0],{i,Length[clause0]}]]];
	
	Score = Function[{cnf0, x0, x1}, 
	Sum[(DistanceToSatisfaction[cnf0[[i]], x0] - DistanceToSatisfaction[cnf0[[i]], x1])* w[cnf0[[i]]],{i,Length[cnf0]}]];
	
	
	atomTruth = Function[atom0, Sign[(polyList/.x)[[atom0[[1]]]]] == Sign[atom0[[2]]]];
	falseAtomList = Select[atomList, atomTruth[#] == False &];
	falseAtomList=Table[falseAtomList[[i,1]]*falseAtomList[[i,2]],{i,Length[falseAtomList]}];
	falseAtomNum=Length[falseAtomList];
	(*Print["false atom list: ", falseAtomList];*)
	
	If[Length[varList]<=2,
		ansMCSAT=Select[MCSATSolver[{{#}},polyList,varList]&/@falseAtomList,#[[1]]!="unsat"&];
		(*Print[ansMCSAT];*)
		If[ansMCSAT!={},Return[ansMCSAT[[1,3]]],Return[x]];
	];
	
	i=1;
	While[i<=Length[varList],
		j=i+1;
		While[j<=Length[varList],
			tempx=x;
			tempx[varList[[i]]] = varList[[i]];
			tempx[varList[[j]]] = varList[[j]];
			(*Print["tempx: ",tempx];*)
			(*Print[{{{#}},polyList/.tempx,Delete[varList,{{i},{j}}]}&/@falseAtomList];*)
			(*ansMCSAT=Select[MCSATSolver[{Append[trueAtomList,#]},polyList/.tempx,{varList[[i]],varList[[j]]}]&/@falseAtomList,#!={"unsat","mcsat"}&];(*falseAtomList\:4e2d\:6bcf\:4e2a\:591a\:9879\:5f0f\:7ea6\:675f\:5173\:4e8exi,xj\:7684\:6837\:672c\:70b9*)
			*)
			(*Print[polyList/.tempx];*)
			ansMCSAT=Select[MCSATSolver[{{#}},polyList/.tempx,{varList[[i]],varList[[j]]}]&/@falseAtomList,#[[1]]!="unsat"&];(*falseAtomList\:4e2d\:6bcf\:4e2a\:591a\:9879\:5f0f\:7ea6\:675f\:5173\:4e8exi,xj\:7684\:6837\:672c\:70b9*)
			(*Print["ansMCSAT: ",ansMCSAT];*)
			(*Print[MaximalBy[Range[Length[ansMCSAT]],Score[cnf,x,ansMCSAT[[#,3]]]&]];*)
			If[ansMCSAT!={},opList=DeleteDuplicates[AppendTo[opList,Union[tempx,ansMCSAT[[MaximalBy[Range[Length[ansMCSAT]],Score[cnf,x,ansMCSAT[[#,3]]]&]]][[1,3]]]]];];
			(*Print["opList: ",opList];*)
			++j;
		];
		++i;
	];
	(*Print["opList\:ff1a ",opList];*)
	xNew=MaximalBy[opList,Score[cnf,x,#]&];
	(*Print["xNew: ",xNew];*)
	If[Length[xNew]>0&&Score[cnf,x,xNew[[1]]]>0,Return[RandomChoice[xNew]],Return[x]];
];


SamplePoint[polyList_, atomList_, assign_]:=
Module[{i, j, poly, isoInterval, samplePoint, midPoint, ans},
	i = 1; ans= <||>;
	While[i <= Length[atomList],
		poly = (polyList[[atomList[[i,1]]]])/.assign;
		(*Print["poly: ",poly];*)
		Which[Length[Variables[Simplify[poly]]] == 1,
		isoInterval = RootIntervals[poly][[1]];
		samplePoint = Flatten[isoInterval];
		midPoint = Table[(samplePoint[[2*i]] + samplePoint[[2*i+1]]) / 2, {i, Length[samplePoint]/2 - 1}];
		samplePoint = Union[samplePoint, midPoint],
		True,
		samplePoint = {};
		];
		
		ans = Append[ans, atomList[[i]] -> samplePoint];
		i++;
	];
	Return[ans];
];


GetAtomInFalseClause[polyList_, cnf_, varList_, x_]:=
Module[{SatAtom, SatClause, falseClause, atom},
	SatAtom = Function[{atom0}, Sign[(polyList[[atom0[[1]]]])/.x] == Sign[atom0[[2]]] ];
	SatClause = Function[{clause0}, Or @@ Map[SatAtom[#]&, clause0]];
	falseClause = Select[cnf, SatClause[#] == False &];
	atom = Union @@ Map[falseClause[[#]]&, Range[Length[falseClause]]];
	Return[atom];
];


GetFalseAtomInTrueClause[polyList_, cnf_, varList_, x_]:=
Module[{SatAtom, SatClause, trueClause, atom, falseAtom},
	SatAtom = Function[{atom0}, Sign[(polyList[[atom0[[1]]]])/.x] == Sign[atom0[[2]]] ];
	SatClause = Function[{clause0}, Or @@ Map[SatAtom[#]&, clause0]];
	trueClause = Select[cnf, SatClause[#] == True &];
	atom = Union @@ Map[trueClause[[#]]&, Range[Length[trueClause]]];
	falseAtom = Select[atom, SatAtom[#] == False &];
	Return[falseAtom];
];


sp = 0.003;


UpdateWeight[polyList_, cnf_, varList_, x_, w_]:=
Module[{wNew, rand, SatAtom, SatClause, falseClause, trueClause, IncreaseWeight},
	wNew = w;
	rand = RandomReal[];
	SatAtom = Function[{atom0}, Sign[(polyList[[atom0[[1]]]])/.x] == Sign[atom0[[2]]] ];
	SatClause = Function[{clause0}, Or @@ Map[SatAtom[#]&, clause0]];
	falseClause = Select[cnf, SatClause[#] == False &];
	trueClause = Select[cnf, SatClause[#] == True && w[#] > 1 &];
	Which[rand >= sp, Scan[wNew[#] += 1 &, falseClause],
	True,Scan[wNew[#] -= 1 &, trueClause]];
	Return[wNew];
];


GradSearchAndApplyOp1[polyList_, cnf_, varList_, x_, w_]:=
Module[{ZeroVecTest, ScalVecTest, gradVecList, i, currVec, RandVec, randvec, randVecList, direction, atomInFalseClause, falseAtomInTrueClause, xNew},
	ZeroVecTest = Function[{vec}, And @@ Map[# == 0 &, vec]];
	ScalVecTest = Function[{vec, vecList}, i = SelectFirst[Range[Length[vec]], vec[[#]] != 0 &]; Or @@ Map[(#[[i]]/vec[[i]])*vec==#&, vecList]];
	gradVecList = Table[Map[D[polyList[[i]],#]&,varList]/.x, {i, Length[polyList]}]; (* \:68af\:5ea6\:5411\:91cf *)
	(*Print["grad vec: ", gradVecList]; *)
	currVec = Values[x]; (* \:5f53\:524d\:70b9\:65b9\:5411 *)
	(*Print["current vec: ", currVec]; *)
	RandVec = Function[RandomInteger[{-1000, 1000}, Length[varList]]]; (* \:751f\:6210\:968f\:673a\:5411\:91cf *)
	(*RandVec = Function[randvec = RandomInteger[{-1000, 1000}, Length[varList]]; If[Count[randvec, 0] < Length[varList] - 1, randvec, RandVec[]]]; \:751f\:6210\:968f\:673a\:5411\:91cf *)
	randVecList = Table[RandVec[], {i,10}];
	(*Print["random vec: ", randVecList]; *)
	direction = Union[gradVecList, {currVec}, randVecList]; 
	(*Print["direction 1: ", direction]; *)
	direction = Delete[direction, Select[Range[Length[direction]], Table[ZeroVecTest[direction[[i]]],{i,Length[direction]}][[#]]&]];
	direction = Delete[direction, Select[Table[{i},{i,Length[direction]}], ScalVecTest[direction[[#1[[1]]]], direction[[1;;#1[[1]]-1]]]&]];(* \:65b9\:5411\:5411\:91cf\:7684\:5217\:8868 *)
	(*Print["direction 2: ", direction]; *)
	
	atomInFalseClause = GetAtomInFalseClause[polyList, cnf, varList, x]; 
	(*Print[atomInFalseClause];*)
	(*Print["GradMaxScoreOp: ",{polyList, cnf, varList, x, w, atomInFalseClause, direction}];*)
    Which[Length[atomInFalseClause] > 0, xNew = GradMaxScoreOp1[polyList, cnf, varList, x, w, atomInFalseClause, direction],
    True, falseAtomInTrueClause = GetFalseAtomInTrueClause[polyList, cnf, varList, x(*, direction*)];
    (*Print["GradMaxScoreOp: ",{polyList, cnf, varList, x, w, atomInFalseClause, direction}];*)
    xNew = GradMaxScoreOp1[polyList, cnf, varList, x, w, falseAtomInTrueClause, direction];
    ];
    Return[{xNew != x, xNew}];
];


GradSearchAndApplyOp2[polyList_, cnf_, varList_, x_, w_]:=
Module[{ZeroVecTest, ScalVecTest, gradVecList, i, currVec, RandVec, randvec, randVecList, direction, atomInFalseClause, falseAtomInTrueClause, xNew},
	ZeroVecTest = Function[{vec}, And @@ Map[# == 0 &, vec]];
	ScalVecTest = Function[{vec, vecList}, i = SelectFirst[Range[Length[vec]], vec[[#]] != 0 &]; Or @@ Map[(#[[i]]/vec[[i]])*vec==#&, vecList]];
	gradVecList = Table[Map[D[polyList[[i]],#]&,varList]/.x, {i, Length[polyList]}]; (* \:68af\:5ea6\:5411\:91cf *)
	(*Print["grad vec: ", gradVecList]; *)
	currVec = Values[x]; (* \:5f53\:524d\:70b9\:65b9\:5411 *)
	(*Print["current vec: ", currVec]; *)
	RandVec = Function[RandomInteger[{-1000, 1000}, Length[varList]]]; (* \:751f\:6210\:968f\:673a\:5411\:91cf *)
	(*RandVec = Function[randvec = RandomInteger[{-1000, 1000}, Length[varList]]; If[Count[randvec, 0] < Length[varList] - 1, randvec, RandVec[]]]; \:751f\:6210\:968f\:673a\:5411\:91cf *)
	randVecList = Table[RandVec[], {i,10}];
	(*Print["random vec: ", randVecList]; *)
	direction = Union[gradVecList, {currVec}, randVecList]; 
	(*Print["direction 1: ", direction]; *)
	direction = Delete[direction, Select[Range[Length[direction]], Table[ZeroVecTest[direction[[i]]],{i,Length[direction]}][[#]]&]];
	direction = Delete[direction, Select[Table[{i},{i,Length[direction]}], ScalVecTest[direction[[#1[[1]]]], direction[[1;;#1[[1]]-1]]]&]];(* \:65b9\:5411\:5411\:91cf\:7684\:5217\:8868 *)
	(*Print["direction 2: ", direction]; *)
	
	atomInFalseClause = GetAtomInFalseClause[polyList, cnf, varList, x]; 
	(*Print[atomInFalseClause];*)
	(*Print["GradMaxScoreOp: ",{polyList, cnf, varList, x, w, atomInFalseClause, direction}];*)
    Which[Length[atomInFalseClause] > 0, xNew = GradMaxScoreOp2[polyList, cnf, varList, x, w, atomInFalseClause, direction],
    True, falseAtomInTrueClause = GetFalseAtomInTrueClause[polyList, cnf, varList, x(*, direction*)];
    (*Print["GradMaxScoreOp: ",{polyList, cnf, varList, x, w, atomInFalseClause, direction}];*)
    xNew = GradMaxScoreOp2[polyList, cnf, varList, x, w, falseAtomInTrueClause, direction];
    ];
    (*Return[{Or@@Table[xNew[[i]]!=x[Keys[xNew][[i]]],{i,Length[xNew]}], xNew}];*)
    Return[{xNew != x,xNew}];
];


GradMaxScoreOp1[polyList_, cnf_, varList_, x_, w_, atomList_, direction_]:=
Module[{i, j, k, DistanceToTruth, DistanceToSatisfaction, Score, atomTruth, falseAtomList, dir, polyListT, samplePoint, tVar, distanceTo0, tNew, xOld, xNew, maxScoreX, t}, 
	DistanceToTruth = Function[{atom0, x0}, 
	Which[Sign[(polyList[[atom0[[1]]]])/.x0] == Sign[atom0[[2]]], 0, 
	True, Abs[(polyList[[atom0[[1]]]])/.x0]+pp]];
	
	DistanceToSatisfaction = Function[{clause0, x0}, Min[Table[DistanceToTruth[clause0[[i]],x0],{i,Length[clause0]}]]];
	
	Score = Function[{cnf0, x0, x1}, 
	Sum[(DistanceToSatisfaction[cnf0[[i]], x0] - DistanceToSatisfaction[cnf0[[i]], x1])* w[cnf0[[i]]],{i,Length[cnf0]}]];
	
	
	atomTruth = Function[atom0, Sign[(polyList/.x)[[atom0[[1]]]]] == Sign[atom0[[2]]]];
	falseAtomList = Select[atomList, atomTruth[#] == False &];
	(*Print["false atom: ", falseAtomList];*)
	i = 1; maxScoreX = x; xOld = x;
	While[i <= Length[direction], 
		dir = direction[[i]];
		(*Print["direction: ",dir];*)
		polyListT = polyList/.Table[varList[[k]] -> x[varList[[k]]] + dir[[k]] * t, {k, Length[varList]}]; (* \:6362\:5143, polyListT\:662f\:5173\:4e8et\:7684\:5355\:53d8\:5143\:591a\:9879\:5f0f\:7684\:5217\:8868 *)
		(*Print["poly list of t: ", polyListT];*)
		samplePoint = SamplePoint[polyListT, falseAtomList, <||>]; (* \:5bf9t\:505a\:5b9e\:6839\:9694\:79bb\:ff0c\:5f97\:5230\:7684\:6837\:672c\:70b9 *)
		(*Print["sample point: ",samplePoint];*)
		j = 1;
		While[j <= Length[falseAtomList],
			Switch[falseAtomList[[j,2]],
				-1,(* \:7ea6\:675f\:4e3ap(x)<0, op\:4e3a\:6cbfdir\:65b9\:5411\:8ddd\:79bb\:539f\:6765\:8d4b\:503c\:6700\:8fd1(t\:8ddd\:79bb0\:6700\:8fd1)\:7684\:8d1f\:6837\:672c\:70b9 *)
				(*Print["switch -1"];*)
				tVar = Select[samplePoint[falseAtomList[[j]]], (polyListT[[falseAtomList[[j,1]]]]/.{t->#}) < 0 &]; (* \:8d1f\:6837\:672c\:70b9 *)
				(*Print["t var: ",tVar];*)
				Which[tVar != {},
				distanceTo0 = Table[Abs[tVar[[k]]], {k, Length[tVar]}]; (* \:8d1f\:6837\:672c\:70b9\:5bf9\:5e94t\:52300\:7684\:8ddd\:79bb *)
				(*tNew = tVar[[Position[distanceTo0, Min[distanceTo0]][[1]][[1]]]];*)
				tNew = tVar[[Position[distanceTo0, Min[distanceTo0]][[1,1]]]];
				xNew =  Association[Table[varList[[k]] -> x[varList[[k]]] + dir[[k]] * tNew, {k, Length[varList]}]];
				(*Print["x new: ",xNew];Print["score: ",Score[cnf, xOld, xNew]];*)
				Which[Score[cnf, xOld, xNew] > 0, maxScoreX = xNew; xOld = xNew;];
				],
				
				1,(* \:7ea6\:675f\:4e3ap(x)>0, op\:4e3a\:6cbfdir\:65b9\:5411\:8ddd\:79bb\:539f\:6765\:8d4b\:503c\:6700\:8fd1(t\:8ddd\:79bb0\:6700\:8fd1)\:7684\:6b63\:6837\:672c\:70b9 *)
				tVar = Select[samplePoint[falseAtomList[[j]]], (polyListT[[falseAtomList[[j,1]]]]/.{t->#}) > 0 &]; (* \:6b63\:6837\:672c\:70b9 *)
				(*Print["t var: ",tVar];*)
				Which[tVar != {},
				distanceTo0 = Table[Abs[tVar[[k]]], {k, Length[tVar]}]; (* \:6b63\:6837\:672c\:70b9\:5bf9\:5e94t\:52300\:7684\:8ddd\:79bb *)
				tNew = tVar[[Position[distanceTo0, Min[distanceTo0]][[1,1]]]];
				xNew =  Association[Table[varList[[k]] -> x[varList[[k]]] + dir[[k]] * tNew, {k, Length[varList]}]];
				(*Print["x new: ",xNew];Print["score: ",Score[cnf, xOld, xNew]];*)
				Which[Score[cnf, xOld, xNew] > 0, maxScoreX = xNew; xOld = xNew;];
				];
				
			];
			j++;
		];
		i++;
	];
	Return[maxScoreX];
];


GradMaxScoreOp2[polyList_, cnf_, varList_, x_, w_, atomList_, direction_]:=
Module[{i, j, k, DistanceToTruth, DistanceToSatisfaction, Score, atomTruth, falseAtomList, falseAtomNum, ansMCSAT, ansMCSATX, opList={}, polyListT, t1, t2, xNew}, 
	DistanceToTruth = Function[{atom0, x0}, 
	Which[Sign[(polyList[[atom0[[1]]]])/.x0] == Sign[atom0[[2]]], 0, 
	True, Abs[(polyList[[atom0[[1]]]])/.x0]+pp]];
	
	DistanceToSatisfaction = Function[{clause0, x0}, Min[Table[DistanceToTruth[clause0[[i]],x0],{i,Length[clause0]}]]];
	
	Score = Function[{cnf0, x0, x1}, 
	Sum[(DistanceToSatisfaction[cnf0[[i]], x0] - DistanceToSatisfaction[cnf0[[i]], x1])* w[cnf0[[i]]],{i,Length[cnf0]}]];
	
	
	atomTruth = Function[atom0, Sign[(polyList/.x)[[atom0[[1]]]]] == Sign[atom0[[2]]]];
	falseAtomList = Select[atomList, atomTruth[#] == False &];
	falseAtomList=Table[falseAtomList[[i,1]]*falseAtomList[[i,2]],{i,Length[falseAtomList]}];
	(*Print["false atom: ", falseAtomList];*)
	falseAtomNum=Length[falseAtomList];
	
	If[Length[varList]<=2,
		ansMCSAT=Select[MCSATSolver[{{#}},polyList,varList]&/@falseAtomList,#[[1]]!="unsat"&];
		(*Print[ansMCSAT];*)
		If[ansMCSAT!={},Return[ansMCSAT[[1,3]]],Return[x]];
	];
	
	i=1;
	While[i<=IntegerPart[Length[direction]/2],
		polyListT=polyList/.Table[varList[[k]] -> x[varList[[k]]] + direction[[2*i-1,k]]*t1 + direction[[2*i,k]]*t2, {k, Length[varList]}]; (* \:6362\:5143, polyListT\:662f\:5173\:4e8et1,t2\:7684\:591a\:9879\:5f0f\:7684\:5217\:8868 *)
		(*Print[polyListT];*)
		ansMCSAT=Select[MCSATSolver[{{#}},polyListT,{t1,t2}]&/@falseAtomList,#[[1]]!="unsat"&];
		(*Print["ansMCSAT: ",ansMCSAT];*)
		ansMCSATX=Table[Association[Table[varList[[k]] -> x[varList[[k]]] + direction[[2*i-1,k]]*ansMCSAT[[j,3]][t1] + direction[[2*i,k]]*ansMCSAT[[j,3]][t2], {k, Length[varList]}]],{j,Length[ansMCSAT]}]; (*falseAtomList\:4e2d\:6bcf\:4e2a\:591a\:9879\:5f0f\:7ea6\:675f\:5173\:4e8ex[2i-1],x[2i]\:7684\:6837\:672c\:70b9*)
		(*Print["ansMCSATX: ",ansMCSATX];*)
		(*AppendTo[opList,MaximalBy[ansMCSATX,Score[cnf,x,#]&]];*)
		opList=Union[opList,ansMCSATX];
		(*Print["opList: ",opList];*)
		++i;
	];
	xNew=MaximalBy[opList,Score[cnf,x,#]&];
	If[Length[xNew]>0&&Score[cnf,x,xNew[[1]]]>0,Return[RandomChoice[xNew]],Return[x]];
];


(* ::Subsubsection:: *)
(*SMT*)
(*\:8f93\:5165\:ff1a\:4e25\:683c\:4e0d\:7b49\:5f0f\:7684\:65e0\:91cf\:8bcd\:5e03\:5c14\:7ec4\:5408*)
(*\:529f\:80fd\:ff1a\:6c42\:89e3SMT\:7684\:878d\:5408\:6c42\:89e3\:5668*)


SMT[formula_]:=
Module[{polyList,cnf,varList},
	cnf=BooleanConvert[formula,"CNF"];
    cnf=If[StringFreeQ[ToString[cnf],"&&"],
        If[StringFreeQ[ToString[cnf],"||"],
            {{cnf}},
            {Table[cnf[[i]],{i,Length[cnf]}]}
        ],
        Table[If[Length[cnf[[i]]]>1,Table[cnf[[i,j]],{j,Length[cnf[[i]]]}],{cnf[[i]]}],{i,Length[cnf]}]
    ];
    (*Print[cnf];*)
	cnf=Table[Table[If[StringContainsQ[ToString[cnf[[i,j]]],">"],{Part[cnf[[i,j]]/. Greater[a_,b_]:>Greater[a-b,0],1],1},{Part[cnf[[i,j]]/. Less[a_,b_]:>Less[a-b,0],1],-1}],{j,Length[cnf[[i]]]}],{i,Length[cnf]}];
	polyList=Union[First/@Flatten[cnf,1]];
	cnf=Table[Table[{Position[polyList,cnf[[i,j,1]]][[1,1]],cnf[[i,j,2]]},{j,Length[cnf[[i]]]}],{i,Length[cnf]}];
	varList=Variables[polyList];
	(*Print[{polyList,cnf,varList}];*)
	Return[Solver[polyList,cnf,varList]];
];


(* ::Subsubsection:: *)
(*Solver*)
(*\:529f\:80fd\:ff1a\:6c42\:89e3SMT\:7684\:878d\:5408\:6c42\:89e3\:5668*)


(*cntLS;*)


(*maxCntLS;*)


Preproc[polyList_, cnf0_, varList_]:=
Module[{Clause1=cnf0,F1=polyList,X=varList,cnf,F2,cons,consZero,highDegMono,highDegPoly,highDegVar,i,j,PRE=1},
	(*\:5904\:7406\:9ad8\:6b21\:5355\:53d8\:91cf\:5355\:9879\:5f0f*)
	highDegMono=Select[Range[Length[MonomialList[F1]]],Length[MonomialList[F1][[#]]]==1&&Max[Exponent[F1[[#]],X]]>1&];
	(*Print["highDegMono: ",highDegMono];*)
	i=1;
	While[i<=Length[highDegMono],
		highDegPoly=F1[[highDegMono[[i]]]];
		(*Print["highDegPoly: ",highDegPoly];*)
		j=1;
		While[j<=Length[Variables[highDegPoly]],
			highDegVar=Variables[highDegPoly][[j]];
			If[Exponent[F1[[highDegMono[[i]]]],highDegVar]>1,
				(*Print["highDegVar: ",highDegVar];*)
				If[EvenQ[Exponent[F1[[highDegMono[[i]]]],highDegVar]],
					(*Print["\:5076\:6570\:6b21"];*)F1[[highDegMono[[i]]]]=F1[[highDegMono[[i]]]]/.{highDegVar-> 1};(*Print["F1: ",F1];*),
					(*Print["\:5947\:6570\:6b21"];*)F1[[highDegMono[[i]]]]=highDegVar*(F1[[highDegMono[[i]]]]/.{highDegVar-> 1});(*Print["F1: ",F1];*)
				];
			];
			++j;
		];
		(*Print["cnf: ",F1];*)
		++i;
	];
	(*Print["F1: ",F1];*)
	
	(*\:5904\:7406\:591a\:9879\:5f0f\:6052\:7b49\:4e8e\:5e38\:6570\:7684\:60c5\:5f62*)            
	cons=Union[Map[{#, -1} &,Select[Range[Length[F1]],Length[Variables[F1[[#]]]]==0&&F1[[#]]<0&]],Map[{#, 1} &, Select[Range[Length[F1]],Length[Variables[F1[[#]]]]==0&&F1[[#]]>0&]]];
	consZero=Select[Range[Length[F1]],Length[Variables[F1[[#]]]]==0&&F1[[#]]==0&];
	(*Print[cons];*)
	cnf=Table[If[Intersection[cons,cnf0[[i]]]=={},cnf0[[i]],Nothing],{i,Length[cnf0]}]/.Table[Table[{cons[[i,1]],-cons[[i,2]]},{i,Length[cons]}][[i]]->Nothing,{i,Length[cons]}](*/.{}->Nothing*)/.Table[Table[{consZero[[i]],1},{i,Length[consZero]}][[i]]->Nothing,{i,Length[consZero]}]/.Table[Table[{consZero[[i]],-1},{i,Length[consZero]}][[i]]->Nothing,{i,Length[consZero]}];
	If[MemberQ[cnf,{}]||cnf=={},PRE=0];  (*UNSAT*)
	F1=ReplacePart[F1, Table[Abs[cons[[i,1]]]->varList[[1]],{i,Length[cons]}]];
	F1=ReplacePart[F1, Table[consZero[[i]]->varList[[1]],{i,Length[consZero]}]];
	(*Print["cnf: ",cnf];
	Print["polyList: ",polyList];*)	
	
	(*Print["preprocessing 1: ",{F1,Clause1,X,PRE}];*)
	Return[{F1,Clause1,X,PRE}];
];


Solver[polyList_, cnf0_, varList_]:=
Module[{ansLs,Clause1,F1,X,a,cc,i,j,xmap=<||>,fmap=<||>,F,Flevel,Fnow,conflictstatelist,Ci,Cli,Clause,Clearn={},
				(*F2,cons,consZero,highDegMono,highDegPoly,highDegVar,*)PRE,
                varnum,Clausenum,assignment=Association[Map[#->0&,varList]],lorder,z,lnum,ML,M,Morder,VC,
                Cstatus,Clstatus,levell,levelc,levelcl,level,tmplevel,tmpc,tmpcl,status,nowc,conflict,
                getFnow,getFlevel,getClause,checkconflict,Polynomialroot,getorder,addl,getF,
                samplecell,getsamplecell,nextsamplecell,
                cnf,LocalSearch,cnt,completeAssignment,maxlevel,lsInit1={},lsInit2={},cntAssign,
                cntLS=0,cad,deg,(*flag,*)maxCntLS,y,(*flag2=True,*)ansLS,cntCAD=0,maxCntCAD},     
                
	{F1,Clause1,X,PRE}=Preproc[polyList, cnf0, varList];
	(*Print["preprocessing: ",{F1,Clause1,X,PRE}];*)
	If[PRE==0,Return[{"unsat","preprocessing"}];];
	Clause1=Table[Table[cnf0[[i,j,1]]*cnf0[[i,j,2]],{j,Length[cnf0[[i]]]}],{i,Length[cnf0]}];
	F=Map[{1,#}&,F1];
	Clause=Clause1;
    (*Print["F1: ",F1];
    Print["Clause: ",Clause];
    Print["X: ",X];*)
    lnum=Length[F1];
    varnum=Length[X];
    deg=Max[Exponent[(MonomialList[F1]/.Association[Map[#->y&,X]]),y]];
    (*Print["deg: ",deg];*)
    (*maxLS=0.5*Min[lnum,deg]*varnum;*)
    (*maxLS=2*(lnum+deg)*varnum;*)
    maxCntLS=0.1*Min[lnum,deg]*varnum;
    (*flag=False;*)
    (*Print["maxCntLS: ",maxCntLS];*)
    (*Print["CAD flag: ",flag];*)
    (*Symmetry Check*)
    (*cntLS=0;*)   
    (*Print["cntLS: ",cntLS];*)       
      
	(*LS + ExtendedLocalSearch + open cad*)
	(*Print["ELS"];*)
	ansLs=ELSSolver[F1, cnf0, varList,10,cntLS,maxCntLS];
	(*Print["cntLS= ",cntLS," maxCntLS= ",maxCntLS];*)
	If[ansLs[[1]]!="unknown",Return[ansLs],cntLS=ansLs[[3]];];
	(*Print["ELS: ",ansLs];*)
	(*Print["MCSAT + Partial Extended Local Search"];*)
    
    Module[{x0=X[[1]],C={}},
    Scan[
        If[(F1/.{#->x0,x0->#})==F1,AppendTo[F,{1,#-x0}];++lnum;AppendTo[C,{-lnum}];x0=#]&
    ,X[[2;;]]];
    (*Print["F (sym): ",F];*)
    (*Print[F];Print[Clause]*)
    If[Length[C]>Length[X]/2,(*Print["Find Symmetry: ",Map[Sequence@@F[[Abs[#],2]]&,C]];*)Clause={Sequence@@C,Sequence@@Clause}]
    ];
    (**)
    Clausenum=Length[Clause];
    
    Scan[(xmap[X[[#]]]=# )&,Range[varnum]];
    Scan[(fmap[F[[#]]]=# )&,Range[lnum]];
    getorder=Function[l,
        Switch[l[[1]],
            1,Max[Map[xmap[#]&,Variables[l[[2]]]]],
            2,Max[Map[xmap[#]&,Variables[l[[2]]]]],
            3,xmap[l[[4]]],
            4,xmap[l[[4]]],
            5,Length[l[[3]]]
        ]
    ];
    Ci=Table[{},varnum];
    Cli=Table[{},varnum];
    levell=Table[{},varnum];
    conflictstatelist=Table[{},varnum];
    (* lorder=Table[If[Length[F[[i]]]>1,xmap[F[[i,3]]],Max[Map[xmap[#]&,Variables[F[[i,1]]]]]],{i,1,lnum}]; *)
     lorder=Map[Max[Map[xmap[#]&,Variables[#[[2]]]]]&,F];
    Scan[AppendTo[Ci[[Max[Map[lorder[[Abs[#]]]&,Clause[[#]]]]]],#]&,Range[Clausenum]];
    Scan[AppendTo[levell[[lorder[[#]]]],#]&,Range[lnum]];
    Flevel=Table[0,lnum];
    Fnow=Table[0,lnum];VC={Table[{},lnum],Table[{},lnum]};
    Cstatus=Table[{0,0},Clausenum];Clstatus={};
    level=1;maxlevel=1;
    ML=Table[{},varnum];
    Morder=Table[0,lnum];M=Table[0,lnum];
    levelc=Table[{},varnum];levelcl=Table[{},varnum];
    conflictstatelist[[level]]={};
    (* Scan[If[Length[F[[#]]]>1,Flevel[[#]]=Polynomialroot[F[[#,1]]/.assignment,Abs[F[[#,2]]]],Flevel[[#]]=F[[#,1]]/.assignment]&,levell[[level]]];     *)
    Scan[(Flevel[[#]]=F1[[#]]/.(X[[1]]->z))&,levell[[level]]];
    (* levelc[[level]]=Select[ Map[{Select[Clause[[#]],lorder[[Abs[#]]]==level& ],#}&,Ci[[level]]], Not[MemberQ[Map[Fnow[[#]]&,Select[Clause[[#[[2]]]],lorder[[Abs[#]]]<level&]],True]]& ]; *)
    levelc[[level]]=Map[{Clause[[#]],#}&,Ci[[level]]];
    For[i=1,i<=Length[levelc[[level]]],++i,
        Scan[AppendTo[VC[[Sign[#],Abs[#]]], levelc[[level,i,2]] ]&,levelc[[level,i,1]]];
        Cstatus[[levelc[[level,i,2]]]]={Length[levelc[[level,i,1]]],0}
    ];
    Polynomialroot[F_,Index_]:=If[Index>CountRoots[F,z],Infinity,Root[F,Index]];
    getsamplecell=Function[{l,a},
        Module[{newl},
            If[Length[a]!=0,
                newl=getF[{5,l,a}];
                ,newl=Nothing];
            newl]];
    nextsamplecell=Function[{lst,a,x0},
        Module[{pc=GetSampleInterval[lst,a,x0],nextl,fg,fl},
            nextl={getsamplecell[pc[[2]],a[[;;-2]]]};
            Scan[(
                    fg=getF[{3,#[[2]]/.(x0->z),#[[3]],x0}];
                    fl=getF[{4,#[[2]]/.(x0->z),#[[3]],x0}];
                    Switch[#[[1]],
                        Greater,AppendTo[nextl,-fg],
                        Equal,AppendTo[nextl,fg];AppendTo[nextl,fl],
                        Less,AppendTo[nextl,-fl]]
                )&,pc[[1]]]; 
            nextl
        ]
    ];
    samplecell=Function[i,If[F[[i,1]]==5 && SameQ[F[[i,4]],False],
        Module[{newlist=If[Length[F[[i,2]]]==1,
                            Pmc[F[[i,2,1]],assignment,X[[lorder[[i]]+1]]],
                            Ps[F[[i,2]],F[[i,3]],X[[lorder[[i]]+1]]]],
                x0=X[[lorder[[i]]]]},
                F[[i,4]]=nextsamplecell[newlist,F[[i,3]],x0];
        ]]];

    getFnow=(Switch[F[[#,1]],
        1,(F[[#,2]]/.assignment)>0,
        2,(F[[#,2]]/.assignment)==0,
        3,assignment[[lorder[[#]]]]>Flevel[[#]],
        4,assignment[[lorder[[#]]]]<Flevel[[#]],
        5,If[assignment[[;;lorder[[#]]]]==F[[#,3]],
            False,
            samplecell[#];
            MemberQ[Map[
              (*  If[F[[Abs[#],1]]==5,
                    !Xor[Fnow[[Abs[#]]],#>0],
                    !Xor[getFnow[Abs[#]],#>0]]&*)
                    (!Xor[Fnow[[Abs[#]]],#>0])&
                    ,F[[#,4]]],True]]
    ])&;
    getFlevel=(Switch[F[[#,1]],
        1,F[[#,2]]/.(X[[level]]->z)/.assignment,
        2,F[[#,2]]/.(X[[level]]->z)/.assignment,
        3,Polynomialroot[F[[#,2]]/.assignment,F[[#,3]]],
        4,Polynomialroot[F[[#,2]]/.assignment,F[[#,3]]],
        _,False
    ])&;
    getClause=Function[{c,l},
        Select[
            Map[{Map[
                    If[lorder[[Abs[#]]]==level,#,
                        !Xor[Fnow[[Abs[#]]],#>0]]&
                ,c[[#]]]/.(False->Nothing),#}&,l],
            Not[MemberQ[#[[1]],True]]&]
    ];
    checkconflict=Function[{list,index},
        Switch[F[[Abs[index],1]],
            1,CheckConflictHalf[list,Flevel[[Abs[index]]],z,index,index>0,False],
            3,CheckConflictHalf[list,Flevel[[Abs[index]]],index,index>0,False],
            4,CheckConflictHalf[list,Flevel[[Abs[index]]],index,index<0,False]]
    ];
    getF=Function[l,
        Module[{ans=fmap[l]},
            If[SameQ[Head[ans],Missing],
                AppendTo[F,l];++lnum;ans=lnum;fmap[l]=lnum;
                If[l[[1]]==5,AppendTo[F[[ans]],False]];
                AppendTo[lorder,getorder[l]];
                AppendTo[levell[[lorder[[ans]]]],lnum];AppendTo[Flevel,0];
                AppendTo[Fnow,0];AppendTo[M,0];
                AppendTo[Morder,0];AppendTo[VC[[1]],{}];AppendTo[VC[[-1]],{}];
                Flevel[[ans]]=getFlevel[ans];
                If[level>lorder[[ans]],Fnow[[ans]]=getFnow[ans]];
                (*Ding: Print*)
                (*Print["F (getF): ",F];*)
            ];
            ans
        ]
    ];
    addl=Function[l,
        Module[{index=l[[1]]},
            M[[Abs[index]]]=Sign[index];AppendTo[ML[[level]],l];Morder[[Abs[index]]]=Length[ML[[level]]];
            Scan[If[#>0,++Cstatus[[#,2]];--Cstatus[[#,1]],++Clstatus[[-#,2]];--Clstatus[[-#,1]]]&,VC[[Sign[index],Abs[index]]]];
            Scan[If[#>0,--Cstatus[[#,1]],--Clstatus[[-#,1]]]&,VC[[-Sign[index],Abs[index]]]];
        ]
    ];
    cntLS=0;
	maxCntCAD=0.75*lnum;
	
    (*flag=varnum<=6;*) 
    (*flag2=False;*)
    While[True,
		tmpc=MinimalBy[Select[Range[Length[levelc[[level]]]],Cstatus[[levelc[[level,#,2]],2]]==0&],Cstatus[[levelc[[level,#,2]],1]]&];
        tmpcl=MinimalBy[Select[Range[Length[levelcl[[level]]]],Clstatus[[levelcl[[level,#,2]],2]]==0&],Clstatus[[levelcl[[level,#,2]],1]]&];
        ++cntCAD;
        If[cntCAD>maxCntCAD,
		    cad=GenericCylindricalDecomposition[And@@Table[Or@@Table[If[Clause[[i,j]]<0,F1[[-Clause[[i,j]]]]<0,F1[[Clause[[i,j]]]]>0],{j,Length[Clause[[i]]]}],{i,Length[Clause]}],X];
            If[cad=={False,False},
                Return[{"unsat","openCAD"}],
                (*Return[{"CAD: sat",FindInstance[cad[[1]],varList]}];*)
                Return[{"sat","openCAD"}];
            ];
        ];
        (*Print["assignment: ",assignment];*)
        If[Length[tmpc]==0 && Length[tmpcl]==0,
            assignment[X[[level]]]=FindMid[conflictstatelist[[level]]];
            (*Ding: Print*)
            (*Print["mcsat: ", assignment];*)
            (* Scan[If[M[[#]]!=0,Fnow[[#]]=M[[#]]>0,If[Length[F[[#]]]>1,If[F[[#,2]]>0,Fnow[[#]]=assignment[X[[level]]]>Flevel[[#]],Fnow[[#]]=assignment[X[[level]]]<Flevel[[#]]],Fnow[[#]]=((F[[#,1]]/.assignment)>0)]]&,levell[[level]]]; *)
            Scan[If[M[[#]]!=0,Fnow[[#]]=M[[#]]>0,If[F[[#,1]]!=5,Fnow[[#]]=getFnow[#]]]&,levell[[level]]];
            Scan[If[M[[#]]==0 && F[[#,1]]==5,Fnow[[#]]=getFnow[#]]&,levell[[level]]];
            
            (*cntAssign=level;*)
            ++level;maxlevel=Max[level,maxlevel];
            (*If[level>varnum,Return[{"sat",assignment}]];*)
            If[level>varnum,Return[{"sat","MCSAT"}]];
            conflictstatelist[[level]]={};
            Scan[(M[[#]]=0)&,levell[[level]]];ML[[level]]={};
            (* Scan[If[Length[F[[#]]]>1,Flevel[[#]]=Polynomialroot[F[[#,1]]/.assignment,Abs[F[[#,2]]]],Flevel[[#]]=F[[#,1]]/.assignment]&,levell[[level]]];     *)
            Scan[(Flevel[[#]]=getFlevel[#])&,levell[[level]]];
            (* levelc[[level]]=Select[ Map[{Select[Clause[[#]],lorder[[Abs[#]]]==level& ],#}&,Ci[[level]]], Not[MemberQ[Map[Fnow[[#]]&,Select[Clause[[#[[2]]]],lorder[[Abs[#]]]<level&]],True]]& ];
            levelcl[[level]]=Select[ Map[{Select[Clearn[[#]],lorder[[Abs[#]]]==level& ],#}&,Cli[[level]]], Not[MemberQ[Map[Fnow[[#]]&,Select[Clearn[[#[[2]]]],lorder[[Abs[#]]]<level&]],True]]& ]; *)
            levelc[[level]]=getClause[Clause,Ci[[level]]];
            levelcl[[level]]=getClause[Clearn,Cli[[level]]];
            Scan[(VC[[1,#]]={};VC[[-1,#]]={})&,levell[[level]] ];
            For[i=1,i<=Length[levelc[[level]]],++i,
                Scan[AppendTo[VC[[Sign[#],Abs[#]]], levelc[[level,i,2]] ]&,levelc[[level,i,1]]];
                Cstatus[[levelc[[level,i,2]]]]={Length[levelc[[level,i,1]]],0}
            ];
            For[i=1,i<=Length[levelcl[[level]]],++i,
                Scan[AppendTo[VC[[Sign[#],Abs[#]]], -levelcl[[level,i,2]] ]&,levelcl[[level,i,1]]];
                Clstatus[[levelcl[[level,i,2]]]]={Length[levelcl[[level,i,1]]],0}
            ];
        ,
            status=-1;
            If[Length[tmpc]>0,
                If[Cstatus[[levelc[[level,tmpc[[1]],2]],1]]==0,status=0;nowc=tmpc[[1]],
                    If[Cstatus[[levelc[[level,tmpc[[1]],2]],1]]==1,status=1;nowc=tmpc[[1]],status=2;nowc=tmpc[[1]]]]
            ];
            If[status!=0 && Length[tmpcl]>0,
                If[Clstatus[[levelcl[[level,tmpcl[[1]],2]],1]]==0,status=0;nowc=-tmpcl[[1]],
                    If[Clstatus[[levelcl[[level,tmpcl[[1]],2]],1]]==1 && status!=1,status=1;nowc=-tmpcl[[1]]];
                    If[status==-1,status=2;nowc=-tmpcl[[1]]]
                ]
            ];
            
            If[status==0,
                If[nowc>0,conflict=Clause[[levelc[[level,nowc,2]]]],conflict=Clearn[[levelcl[[level,-nowc,2]]]]];
                (*Ding: Print*)
                (*Print["conflict: ",conflict];*)
                While[status==0,
                    For[a = Select[conflict, lorder[[Abs[#]]]==level && M[[Abs[#]]]!=0 && Length[ML[[level,Morder[[Abs[#]]]]]] == 2 &],Length[a] != 0, 
                               a = Select[conflict, lorder[[Abs[#]]]==level && M[[Abs[#]]]!=0 && Length[ML[[level,Morder[[Abs[#]]]]]] == 2 &],
                        conflict = Fold[ClauseResolve[#1, ML[[level,Morder[[Abs[#2]]],2]], #2] &, conflict, a];
                    ];
                    (*Ding: Print*)
                    (*Print["conflict: ",conflict];*)
                    If[Length[conflict]==0,Return[{"unsat","MCSAT"(*,lnum,deg,varnum,cntCAD*)}]];                    
                    
                    tmplevel=Max[Map[lorder[[Abs[#]]]&,conflict]];
                    
                    If[tmplevel==level,
                        a=Select[conflict,(lorder[[Abs[#]]]==level && F[[Abs[#],1]]==5)&];
                        If[Length[a]!=0,
                            (* Scan[samplecell[#]&,a];
                            If[Length[a]==1 || level==1,
                                conflict=DeleteDuplicates[
                                Fold[(If[#2<0,Print["error:",  #, " in conflict ."]];
                                #1/.(#2->Sequence@@F[[#2,4]]))&
                                ,conflict,a]]; 
                            ,
                                Module[{c=<||>},
                                    conflict=Select[conflict,(lorder[[Abs[#]]]!=level || F[[Abs[#],1]]!=5)&];
                                    Scan[If[SameQ[Head[c[F[[#,3]]]],Missing],c[F[[#,3]]]={#},AppendTo[c[F[[#,3]]],#]]&,a];
                                    c=List@@c;
                                    c=Map[nextsamplecell[DeleteDuplicates[Flatten[Map[(F[[F[[#,4,1]],2]])&,#]]],F[[#[[1]],3]],X[[level]]]&,c];
                                    conflict=DeleteDuplicates[Flatten[{conflict,c}]];
                                ];
                            ]; *)
                            conflict=DeleteDuplicates[
                                Fold[(If[#2<0,Print["error:",  #, " in conflict ."]];
                                samplecell[#2];#1/.(#2->Sequence@@F[[#2,4]]))&
                                ,conflict,a]];
                            (*Ding: Print*)
                            (*Print["conflict: ",conflict];*)
                            tmplevel=Max[Map[lorder[[Abs[#]]]&,conflict]];
                            ,
                            AppendTo[Clearn,conflict];
                            (*Ding: Print*)
                            (*Print["Clearn: ",Clearn];*)
                            AppendTo[Cli[[level]],Length[Clearn]];
                            Scan[AppendTo[VC[[Sign[#],Abs[#] ]],-Length[Clearn]]&, Select[conflict,lorder[[Abs[#]]]==level& ] ];
                            a=Select[conflict,lorder[[Abs[#]]]==level&];
                            AppendTo[levelcl[[level]],{a,Length[Clearn]}];
                            AppendTo[Clstatus,{Length[Select[a,M[[Abs[#]]]==0&]],0}];
                            If[Clstatus[[-1,1]]<2,status=1,status=2];
                            nowc=-Length[levelcl[[level]]];
                            If[Clstatus[[-1,1]]==0,
                                If[Length[a]==1,a=Max[Map[Morder[[Abs[#]]]&,a]]-1,
                                    a=RankedMax[Map[Morder[[Abs[#]]]&,a],2]];
                                Scan[
                                    (M[[Abs[#[[1]]]]]=0;
                                    Scan[If[#>0,--Cstatus[[#,2]];++Cstatus[[#,1]],--Clstatus[[-#,2]];++Clstatus[[-#,1]]]&,VC[[Sign[#[[1]]],Abs[#[[1]]]]]];
                                    Scan[If[#>0,++Cstatus[[#,1]],++Clstatus[[-#,1]]]&,VC[[-Sign[#[[1]]],Abs[#[[1]]]]]];)&
                                ,ML[[level,a+1;;]]];
                                ML[[level]]=ML[[level,;;a]];
                                (* conflictstatelist[[level]]=Fold[
                                    If[Length[F[[Abs[#2[[1]]]]]]==1,
                                    CheckConflictHalf[#1,Flevel[[Abs[#2[[1]]]]],X[[level]],#2[[1]],#2[[1]]>0,False][[2]],
                                    CheckConflictHalf[#1,Flevel[[Abs[#2[[1]]]]],#2[[1]],!Xor[F[[Abs[#2[[1]]],2]]>0,#2[[1]]>0],False][[2]]]&
                                ,{},ML[[level]]]]; *)
                                conflictstatelist[[level]]=Fold[checkconflict[#1,#2[[1]]][[2]]&,{},ML[[level]]]]]];
                    level=tmplevel;
                ]
            ];
            (*Ding: local search solver -- begin*)
            (*Print["BEGIN: mcsat-exLS"];*)
            (*Print["mcsat: ",assignment];*)
            maxlevel=Max[maxlevel,level];
            (*Print["cntAssign=",cntAssign,", Min=",Min[0.4*varnum,0.9*maxlevel]];
            Print["cntLS: ",cntLS,", maxCntLS: ",maxCntLS];*)
            cntAssign=level-1;
            If[cntAssign>Min[0.4*varnum,0.9*maxlevel]&&cntLS<maxCntLS,
                (*cnt=1;*)
                (*fail={};*)
                (*completeAssignment = assignment;*)
                completeAssignment=<||>;
                If[cntAssign==varnum-1, 
                    (* \:53ea\:67091\:4e2a\:672a\:8d4b\:503c\:53d8\:91cf: 1\:6b21\:4e0d\:6539\:53d8\:90e8\:5206\:8d4b\:503c\:7684LocalSearch *)
                    Scan[(completeAssignment[#]=1)&,X[[cntAssign+1;;]]];
                    (*Print["lsInit1: ",lsInit1];
                    Print["assignment: ",assignment];*)
                    If[Not[MemberQ[lsInit1,assignment]],
                        AppendTo[lsInit1,assignment];
                        (*Print["ExtendedLS: ",{F1/.Take[Normal[assignment],cntAssign],cnf0,Take[X,-(varnum-cntAssign)],1,cntLS,maxCntLS}];*)
                        ansLS=ELSSolver[F1/.Take[Normal[assignment],cntAssign],cnf0,Take[X,-(varnum-cntAssign)],1,cntLS,maxCntLS];
                        If[Length[ansLS]>=3,cntLS=ansLS[[3]]];
                        (*Print["assignment: ",assignment];*)
                        (*Print["completeAssignment: ",completeAssignment];*)
                        (*Print["ansLS: ",ansLS];*)
                        If[ansLS[[1]]=="sat",(*Print["ansLS: ",ansLS];*)Return[{"sat","mcsat-ELS"}];cntLS=ansLS[[3]];];
                        (*Print["END: exLS"];*)
                    ],
                    (*\:591a\:4e2a\:672a\:8d4b\:503c\:53d8\:91cf: 3\:6b21\:4e0d\:6539\:53d8\:90e8\:5206\:8d4b\:503c\:7684LocalSearch *)
                    Scan[(completeAssignment[#]=1)&,X[[cntAssign+1;;]]];
                    (*Print["completeAssignment: ",completeAssignment];*)
                    If[Not[MemberQ[lsInit1,{assignment,completeAssignment}]],
                        AppendTo[lsInit1,{assignment,completeAssignment}];
                        (*Print["ExtendedLS: ",{F1/.Take[Normal[assignment],cntAssign],cnf0,Take[X,-(varnum-cntAssign)],1,cntLS,maxCntLS}];*)
                        ansLS=ELSSolver[F1/.Take[Normal[assignment],cntAssign],cnf0,Take[X,-(varnum-cntAssign)],3,cntLS,maxCntLS];
                        If[Length[ansLS]>=3,cntLS=ansLS[[3]]];
                        (*Print["ExtendedLS: ",{F1/.Take[Normal[assignment],cntAssign],cnf0,Take[X,-(varnum-cntAssign)],1,cntLS,maxCntLS}];*)
                        (*Print["ansLS: ",ansLS];*)
                        If[ansLS[[1]]=="sat",(*Print["ansLS: ",ansLS];*)Return[{"sat","mcsat-ELS"}];cntLS=ansLS[[3]];];
                        (*Print["END: exLS"];*)
                    ];
                ];
            ];
            (*Ding: local search solver -- end*)
            (*Print["END: mcsat-exLS"];*)
            
            If[nowc>0,cc=levelc[[level,nowc,1]],cc=levelcl[[level,-nowc,1]]];
            If[status==1,
                a=Select[cc,M[[Abs[#]]]==0&][[1]];
            ,
                a=MaximalBy[Select[cc,M[[Abs[#]]]==0&],Length[Select[VC[[Sign[#],Abs[#]]],If[#<0,Clstatus[[-#,2]]==0,Cstatus[[#,2]]==0]&]]&][[1]];
            ];
            (* If[Length[F[[Abs[a]]]]==1,
                tmpc=CheckConflictHalf[conflictstatelist[[level]],Flevel[[Abs[a]]],X[[level]],a,a>0,False];
            ,
                tmpc=CheckConflictHalf[conflictstatelist[[level]],Flevel[[Abs[a]]],a,!Xor[F[[Abs[a],2]]>0,a>0],False];
            ]; *)
            tmpc=checkconflict[conflictstatelist[[level]],a];
            If[tmpc[[1]],
                conflictstatelist[[level]]=tmpc[[2]];
                If[nowc>0,cc=Clause[[levelc[[level,nowc,2]]]],cc=Clearn[[levelcl[[level,-nowc,2]]]]];
            ,
                cc=DeleteDuplicates[Map[#[[4]]&,tmpc[[2]]]];
                If[level>1,
                    Module[{l},
                        l=Map[Function[x,
                                If[F[[Abs[x],1]]==1 || F[[Abs[x],1]]==2,
                                    F[[Abs[x],2]],
                                    F[[Abs[x],2]]/.(z->X[[level]])]]
                            ,cc];
                        l=Select[DeleteDuplicates[Flatten[Map[FactorList,l][[All,All,1]]]],UnsameQ[Variables[#],{}]&];
                        conflict=getsamplecell[{l},assignment[[;;level-1]]];
                        (*Ding: Print*)
                        (*Print["conflict: ",conflict];*)
                    ]
                    ,
                    conflict=Nothing;
                    (*Ding: Print*)
                     (*Print["conflict: ",conflict];*)
                ];
                (* cc=Flatten[{conflict,Map[Minus,cc]}];  *)
                cc={Sequence@@Map[Minus,cc],conflict};
                a=-a;
                status=1;
            ];
            If[status==1,addl[{a,cc}],addl[{a}]];
            (* M[[Abs[a]]]=Sign[a];
            If[status==1,AppendTo[ML[[level]],{a,cc}],AppendTo[ML[[level]],{a}]];
            Morder[[Abs[a]]]=Length[ML[[level]]];
            Scan[If[#>0,++Cstatus[[#,2]];--Cstatus[[#,1]],++Clstatus[[-#,2]];--Clstatus[[-#,1]]]&,VC[[Sign[a],Abs[a]]]];
            Scan[If[#>0,--Cstatus[[#,1]],--Clstatus[[-#,1]]]&,VC[[-Sign[a],Abs[a]]]]; *)
            (* Theoretical reasoning *)
            (* If[Length[F[[Abs[a]]]]>1 && UnsameQ[Head[status=fmap[{F[[Abs[a],1]],-F[[Abs[a],2]],F[[Abs[a],3]]}]],Missing] && M[[status]]==0 , *)
            If[F[[Abs[a],1]]==3 || F[[Abs[a],1]]==4,
                status=getF[{7-F[[Abs[a],1]],Sequence@@F[[Abs[a],2;;]]}];
                If[M[[status]]==0,cc=a;a=-1*Sign[a]*status;cc={a,-cc};addl[{a,cc}];]
                (* M[[Abs[a]]]=Sign[a];AppendTo[ML[[level]],{a,cc}];Morder[[Abs[a]]]=Length[ML[[level]]];
                Scan[If[#>0,++Cstatus[[#,2]];--Cstatus[[#,1]],++Clstatus[[-#,2]];--Clstatus[[-#,1]]]&,VC[[Sign[a],Abs[a]]]];
                Scan[If[#>0,--Cstatus[[#,1]],--Clstatus[[-#,1]]]&,VC[[-Sign[a],Abs[a]]]]; *)
            ]
        ]

    ]
];


(* ::Subsubsection:: *)
(*ELSSolver*)
(*\:529f\:80fd\:ff1a\:6c42\:89e3SMT\:7684\:6269\:5c55\:5c40\:90e8\:641c\:7d22\:6c42\:89e3\:5668\:ff0c\:524d\:4e24\:7ea7\:7b56\:7565\:662fLS\:7684celljump\:ff0c\:540e\:4e24\:7ea7\:7b56\:7565\:662fExtendedLS\:7684celljump*)


ELSSolver[polyList0_, cnf0_, varList_,lsLimit_,cntLS0_,maxCntLS_]:=
Module[{cnt=1,init,lsInit={},ans,cons,consZero,polyList,cnf,LenDenNum,
		lnum,varnum,deg(*,cntELS,maxCntELS*),cntLS=cntLS0},
	
	(*\:5904\:7406\:591a\:9879\:5f0f\:6052\:7b49\:4e8e\:5e38\:6570\:7684\:60c5\:5f62*)            
	cons=Union[Map[{#, -1} &,Select[Range[Length[polyList0]],Length[Variables[polyList0[[#]]]]==0&&polyList0[[#]]<0&]],Map[{#, 1} &, Select[Range[Length[polyList0]],Length[Variables[polyList0[[#]]]]==0&&polyList0[[#]]>0&]]];
	consZero=Select[Range[Length[polyList0]],Length[Variables[polyList0[[#]]]]==0&&polyList0[[#]]==0&];
	(*Print[cons];*)
	cnf=Table[If[Intersection[cons,cnf0[[i]]]=={},cnf0[[i]],Nothing],{i,Length[cnf0]}]/.Table[Table[{cons[[i,1]],-cons[[i,2]]},{i,Length[cons]}][[i]]->Nothing,{i,Length[cons]}](*/.{}->Nothing*)/.Table[Table[{consZero[[i]],1},{i,Length[consZero]}][[i]]->Nothing,{i,Length[consZero]}]/.Table[Table[{consZero[[i]],-1},{i,Length[consZero]}][[i]]->Nothing,{i,Length[consZero]}];
	If[MemberQ[cnf,{}]||cnf=={},Return[{"unsat","There are constants that cannot be satisfied."}]];
	polyList=ReplacePart[polyList0, Table[Abs[cons[[i,1]]]->varList[[1]],{i,Length[cons]}]];
	polyList=ReplacePart[polyList, Table[consZero[[i]]->varList[[1]],{i,Length[consZero]}]];
	(*Print["cnf: ",cnf];
	Print["polyList: ",polyList];*)
	
	While[cnt<=lsLimit,
		Which[cnt==1,
			(*Print["ELS start: ",cnt];*)
			init=Association[Map[#->1&,varList]];
			AppendTo[lsInit,init];
			ans=ELS[init,polyList,cnf,varList,cntLS,maxCntLS];
            If[ans[[1]]!="unknown",Return[ans],cntLS=ans[[3]];];
			++cnt,
			cnt>=2&&cnt<=6,
			(*Print["ELS start: ",cnt];*)
			init=Association[Map[#->RandomChoice[{-1,1}]&,varList]];
			If[Not[MemberQ[lsInit,init]],
                AppendTo[lsInit,init];
                ans=ELS[init,polyList,cnf,varList,cntLS,maxCntLS];
                If[ans[[1]]!="unknown",Return[ans],cntLS=ans[[3]];];
            ];
            ++cnt,
            cnt>=7,
            (*Print["ELS start: ",cnt];*)
            init=Association[Map[#->RandomInteger[{-50*(cnt-6),50*(cnt-6)}]&,varList]];
            If[Not[MemberQ[lsInit,init]],
                AppendTo[lsInit,init];
                ans=ELS[init,polyList,cnf,varList,cntLS,maxCntLS];
                If[ans[[1]]!="unknown",Return[ans],cntLS=ans[[3]];];
            ];
            ++cnt;
		];
	];
	Return[{"unknown","ELS",cntLS}];
];


(*ELS[x0_, polyList_, cnf_, varList_,cntLS0_,maxCntLS_]:=
Module[{i, x, w, isAxis, x1, x2, isDir,
		cnt=1,init,lsInit={},(*maxCntLS,*)varListLast,vars=Length[varList],varList2,
		clauses,y,cons,consZero,cycle={},cad,mcsatPoly,LenDenNum,cntLS=cntLS0,varnum=Length[varList]},
	
	clauses=Table[Table[cnf[[i,j,1]]*cnf[[i,j,2]],{j,Length[cnf[[i]]]}],{i,Length[cnf]}];
	
	If[vars<=2,Return[MCSATSolver[clauses,polyList,varList]]];
	varList2=Take[varList,vars-2];
	varListLast=Take[varList,-2];
	
	(*maxCntLS=2*Min[Length[polyList],Max[Exponent[(MonomialList[polyList]/.Association[Map[#->y&,varList]]),y]]]*vars;*)
	(*Print["maxCntLS: ",maxCntLS];*)
	x = x0;
	w = Association[Table[cnf[[i]] -> 1, {i, Length[cnf]}]];
	(*Print["initial x: ", x];*)
	
	While[True,
		If[SatCheck[polyList, cnf, varList, x],Return[{"sat","ELS"}]];
		x1=x;
		x1[varListLast[[1]]]=varListLast[[1]];
		x1[varListLast[[2]]]=varListLast[[2]];
		mcsatPoly=polyList/.x1;
		(*Print[mcsatPoly];*)
		If[MCSATSolver[clauses,mcsatPoly,varListLast][[1]]=="sat",Return[{"sat","ELS"}]];
		(*Print["cntLS=",cntLS," maxCntLS=",maxCntLS];*)
		If[cntLS>maxCntLS,
		    cad=GenericCylindricalDecomposition[And@@Table[Or@@Table[If[cnf[[i,j,2]]<0,polyList[[cnf[[i,j,1]]]]<0,polyList[[cnf[[i,j,1]]]]>0],{j,Length[cnf[[i]]]}],{i,Length[cnf]}],varList];
            If[cad=={False,False},
                Return[{"unsat","openCAD"}],
                (*Return[{"CAD: sat",FindInstance[cad[[1]],varList]}];*)
                Return[{"sat","openCAD"}];
            ];
        ];
        ++cntLS;
        (*Print["cntLS: ",cntLS];*)
		{isAxis, x1} = SearchAndApplyOp1[polyList, cnf, varList, x, w]; (* \:6cbf\:5750\:6807\:8f74celljump 1 *)
		(*Print["celljump axis 1: ",isAxis,x1];*)
		i=1;
		While[i<=varnum,
			If[Max[IntegerLength[Denominator[x1[[i]]]],IntegerLength[Abs[Numerator[x1[[i]]]]]]>5,
				(*Print["simplify"];*)
				LenDenNum=Min[IntegerLength[Denominator[x1[[i]]]],IntegerLength[Abs[Numerator[x1[[i]]]]]];
				x1[[i]]=IntegerPart[Numerator[x1[[i]]]/10^(LenDenNum-2)]/IntegerPart[Denominator[x1[[i]]]/10^(LenDenNum-2)];
			];
			If[IntegerLength[Denominator[x1[[i]]]]>5,x1[[i]]=0;];
			++i;
		];
		Print["celljump axis 1 - simplify: ",isAxis,x1];
		If[isAxis&&Not[MemberQ[cycle,x1]], AppendTo[cycle,x1]; x = x1,
			w = UpdateWeight[polyList, cnf, varList, x, w];
			(*Print["cntLS=",cntLS," maxCntLS=",maxCntLS];*)
			If[cntLS>maxCntLS,
		        cad=GenericCylindricalDecomposition[And@@Table[Or@@Table[If[cnf[[i,j,2]]<0,polyList[[cnf[[i,j,1]]]]<0,polyList[[cnf[[i,j,1]]]]>0],{j,Length[cnf[[i]]]}],{i,Length[cnf]}],varList];
                If[cad=={False,False},
                    Return[{"unsat","openCAD"}],
                    (*Return[{"CAD: sat",FindInstance[cad[[1]],varList]}];*)
                    Return[{"sat","openCAD"}];
                ];
            ];
            ++cntLS;
            (*Print["cntLS: ",cntLS];*)
			{isDir, x1} = GradSearchAndApplyOp1[polyList, cnf, varList, x, w]; (* \:6cbf\:67d0\:4e9b\:65b9\:5411celljump 1 *)
			(*If[Max[Denominator[Values[x1]]]>10^20||Max[Abs[Numerator[Values[x1]]]]>10^20,Break[]];*)
			(*Print["celljump direction 1: ",isDir,x1];*)
			(*Print["Denominator Length: ",IntegerLength[Denominator[x1[[1]]]]];*)
			i=1;
			While[i<=varnum,
				If[Max[IntegerLength[Denominator[x1[[i]]]],IntegerLength[Abs[Numerator[x1[[i]]]]]]>5,
					(*Print["simplify"];*)
					LenDenNum=Min[IntegerLength[Denominator[x1[[i]]]],IntegerLength[Abs[Numerator[x1[[i]]]]]];
					x1[[i]]=IntegerPart[Numerator[x1[[i]]]/10^(LenDenNum-2)]/IntegerPart[Denominator[x1[[i]]]/10^(LenDenNum-2)];
				];
				If[IntegerLength[Denominator[x1[[i]]]]>5,x1[[i]]=0;];
				++i;
			];
			Print["celljump direction 1 - simplify: ",isDir,x1];
			If[isDir&&Not[MemberQ[cycle,x1]], AppendTo[cycle,x1]; x = x1,
				(*Print["cntLS=",cntLS," maxCntLS=",maxCntLS];*)
				If[cntLS>maxCntLS,
		            cad=GenericCylindricalDecomposition[And@@Table[Or@@Table[If[cnf[[i,j,2]]<0,polyList[[cnf[[i,j,1]]]]<0,polyList[[cnf[[i,j,1]]]]>0],{j,Length[cnf[[i]]]}],{i,Length[cnf]}],varList];
                    If[cad=={False,False},
                        Return[{"unsat","openCAD"}],
                        (*Return[{"CAD: sat",FindInstance[cad[[1]],varList]}];*)
                        Return[{"sat","openCAD"}];
                    ];
                ];
                ++cntLS;
                (*Print["cntLS: ",cntLS];*)
                (*Print["celljump axis 2"];*)
				{isAxis, x1} = SearchAndApplyOp2[polyList, cnf, varList, x, w]; (* \:6cbf\:5750\:6807\:8f74celljump 2 *)
				(*Print["celljump axis 2: ",isAxis,x2];*)
				i=1;
				While[i<=varnum,
					If[Max[IntegerLength[Denominator[x1[[i]]]],IntegerLength[Abs[Numerator[x1[[i]]]]]]>5,
						(*Print["simplify"];*)
						LenDenNum=Min[IntegerLength[Denominator[x1[[i]]]],IntegerLength[Abs[Numerator[x1[[i]]]]]];
						x1[[i]]=IntegerPart[Numerator[x1[[i]]]/10^(LenDenNum-2)]/IntegerPart[Denominator[x1[[i]]]/10^(LenDenNum-2)];
					];
					If[IntegerLength[Denominator[x1[[i]]]]>5,x1[[i]]=0;];
					++i;
				];
				x2=x;
				If[Length[varList2]>=2,
					x2[varList2[[1]]]=x1[varList2[[1]]];
					x2[varList2[[2]]]=x1[varList2[[2]]],
					x2[varList2[[1]]]=x1[varList2[[1]]];
				];
				Print["celljump axis 2 - simplify: ",isAxis,x2];
				If[isAxis&&Not[MemberQ[cycle,x2]], 
				    AppendTo[cycle,x2]; x = x2, 
				    (*Print["cycle: ",cycle];*)
				    (*Print["mcsat: ",{clauses,mcsatPoly,varListLast}];*)
				    (*Print["mcsatPoly: ",mcsatPoly];*)
		            (*Print["mcsat: ",{clauses,mcsatPoly,varListLast}];*)
		            (*If[MCSATSolver[clauses,mcsatPoly,varListLast][[1]]=="sat",Return[{"sat","ELS-mcsat"}]],*)
		        
		            (*If[MCSATSolver[clauses,Table[If[Length[Variables[mcsatPoly[[i]]]]==0,varListLast[[1]],mcsatPoly[[i]]],{i,Length[mcsatPoly]}],varListLast][[1]]=="sat",Return[{"sat","exLS-mcsat"}]],*)

		            (*Print["cntLS=",cntLS," maxCntLS=",maxCntLS];*)
					If[cntLS>maxCntLS,
					    (*Print[{And@@Table[Or@@Table[If[cnf0[[i,j,2]]<0,polyList0[[cnf0[[i,j,1]]]]<0,polyList0[[cnf0[[i,j,1]]]]>0],{j,Length[cnf0[[i]]]}],{i,Length[cnf0]}],varList}];*)
                        cad=GenericCylindricalDecomposition[And@@Table[Or@@Table[If[cnf[[i,j,2]]<0,polyList[[cnf[[i,j,1]]]]<0,polyList[[cnf[[i,j,1]]]]>0],{j,Length[cnf[[i]]]}],{i,Length[cnf]}],varList];
                        If[cad=={False,False},
                            Return[{"unsat","openCAD"}],
                            (*Return[{"CAD: sat",FindInstance[cad[[1]],varList]}];*)
                            Return[{"sat","openCAD"}];
                        ];
                    ];
                    ++cntLS;
                    (*Print["cntLS: ",cntLS];*)
                    (*Print["cntLS: ",cntLS];*)
				    w = UpdateWeight[polyList, cnf, varList2, x, w];
                    {isDir, x1} = GradSearchAndApplyOp2[polyList, cnf, varList, x, w]; (* \:6cbf\:67d0\:4e9b\:65b9\:5411celljump 2 *)
					(*Print["celljump direction 2: ",isDir,x2];*)
					i=1;
					While[i<=varnum,
						If[Max[IntegerLength[Denominator[x1[[i]]]],IntegerLength[Abs[Numerator[x1[[i]]]]]]>5,
							(*Print["simplify"];*)
							LenDenNum=Min[IntegerLength[Denominator[x1[[i]]]],IntegerLength[Abs[Numerator[x1[[i]]]]]];
							x1[[i]]=IntegerPart[Numerator[x1[[i]]]/10^(LenDenNum-2)]/IntegerPart[Denominator[x1[[i]]]/10^(LenDenNum-2)];
						];
						If[IntegerLength[Denominator[x1[[i]]]]>5,x1[[i]]=0;];
						++i;
					];
					x2=x;
				    If[Length[varList2]>=2,
						x2[varList2[[1]]]=x1[varList2[[1]]];
						x2[varList2[[2]]]=x1[varList2[[2]]],
						x2[varList2[[1]]]=x1[varList2[[1]]];
					];
					Print["celljump direction 2 - simplify: ",isDir,x2];
				    If[MemberQ[cycle,x2],(*Print["cycle"];*)Break[]];
				    If[isDir,AppendTo[cycle,x2]; x = x2,
				        (*Print["cycle: ",cycle];*)
						(*mcsatPoly=polyList/.x;*)
		                (*Print["mcsat: ",{clauses,mcsatPoly,varListLast}];*)
		                (*If[MCSATSolver[clauses,mcsatPoly,varListLast][[1]]=="sat",Return[{"sat","exLS-mcsat"}]],*)
				        Break[];
					];
				];
			];
		];
	];
	Return[{"unknown","ELS",cntLS}];
];*)


ELS[x0_, polyList_, cnf_, varList_,cntLS0_,maxCntLS_]:=
Module[{i, x, w, isAxis, x1, x2, isDir,
		cnt=1,init,lsInit={},(*maxCntLS,*)varListLast,vars=Length[varList],varList2,
		clauses,y,cons,consZero,cycle={},cad,mcsatPoly,LenDenNum,cntLS=cntLS0,varnum=Length[varList]},
	
	clauses=Table[Table[cnf[[i,j,1]]*cnf[[i,j,2]],{j,Length[cnf[[i]]]}],{i,Length[cnf]}];
	
	If[vars<=2,Return[MCSATSolver[clauses,polyList,varList]]];
	varList2=Take[varList,vars-2];
	varListLast=Take[varList,-2];
	
	(*maxCntLS=2*Min[Length[polyList],Max[Exponent[(MonomialList[polyList]/.Association[Map[#->y&,varList]]),y]]]*vars;*)
	(*Print["maxCntLS: ",maxCntLS];*)
	x = x0;
	w = Association[Table[cnf[[i]] -> 1, {i, Length[cnf]}]];
	(*Print["initial x: ", x];*)
	
	While[True,
		If[SatCheck[polyList, cnf, varList, x],Return[{"sat","ELS"}]];
		x1=x;
		x1[varListLast[[1]]]=varListLast[[1]];
		x1[varListLast[[2]]]=varListLast[[2]];
		mcsatPoly=polyList/.x1;
		(*Print[mcsatPoly];*)
		If[MCSATSolver[clauses,mcsatPoly,varListLast][[1]]=="sat",Return[{"sat","ELS"}]];
		(*Print["cntLS=",cntLS," maxCntLS=",maxCntLS];*)
		If[cntLS>maxCntLS,
		    cad=GenericCylindricalDecomposition[And@@Table[Or@@Table[If[cnf[[i,j,2]]<0,polyList[[cnf[[i,j,1]]]]<0,polyList[[cnf[[i,j,1]]]]>0],{j,Length[cnf[[i]]]}],{i,Length[cnf]}],varList];
            If[cad=={False,False},
                Return[{"unsat","openCAD"}],
                (*Return[{"CAD: sat",FindInstance[cad[[1]],varList]}];*)
                Return[{"sat","openCAD"}];
            ];
        ];
        ++cntLS;
        (*Print["cntLS: ",cntLS];*)
		{isAxis, x1} = SearchAndApplyOp1[polyList, cnf, varList, x, w]; (* \:6cbf\:5750\:6807\:8f74celljump 1 *)
		(*Print["celljump axis 1: ",isAxis,x1];*)
		i=1;
		While[i<=varnum,
			If[Max[IntegerLength[Denominator[x1[[i]]]],IntegerLength[Abs[Numerator[x1[[i]]]]]]>5,
				(*Print["simplify"];*)
				LenDenNum=Min[IntegerLength[Denominator[x1[[i]]]],IntegerLength[Abs[Numerator[x1[[i]]]]]];
				x1[[i]]=IntegerPart[Numerator[x1[[i]]]/10^(LenDenNum-2)]/IntegerPart[Denominator[x1[[i]]]/10^(LenDenNum-2)];
			];
			If[IntegerLength[Denominator[x1[[i]]]]>5,x1[[i]]=0;];
			++i;
		];
		(*Print["celljump axis 1 - simplify: ",isAxis,x1];*)
		If[isAxis&&Not[MemberQ[cycle,x1]], AppendTo[cycle,x1]; x = x1,
			w = UpdateWeight[polyList, cnf, varList, x, w];
			(*Print["cntLS=",cntLS," maxCntLS=",maxCntLS];*)
			If[cntLS>maxCntLS,
		        cad=GenericCylindricalDecomposition[And@@Table[Or@@Table[If[cnf[[i,j,2]]<0,polyList[[cnf[[i,j,1]]]]<0,polyList[[cnf[[i,j,1]]]]>0],{j,Length[cnf[[i]]]}],{i,Length[cnf]}],varList];
                If[cad=={False,False},
                    Return[{"unsat","openCAD"}],
                    (*Return[{"CAD: sat",FindInstance[cad[[1]],varList]}];*)
                    Return[{"sat","openCAD"}];
                ];
            ];
            ++cntLS;
            (*Print["cntLS: ",cntLS];*)
			{isDir, x1} = GradSearchAndApplyOp1[polyList, cnf, varList, x, w]; (* \:6cbf\:67d0\:4e9b\:65b9\:5411celljump 1 *)
			(*If[Max[Denominator[Values[x1]]]>10^20||Max[Abs[Numerator[Values[x1]]]]>10^20,Break[]];*)
			(*Print["celljump direction 1: ",isDir,x1];*)
			(*Print["Denominator Length: ",IntegerLength[Denominator[x1[[1]]]]];*)
			i=1;
			While[i<=varnum,
				If[Max[IntegerLength[Denominator[x1[[i]]]],IntegerLength[Abs[Numerator[x1[[i]]]]]]>5,
					(*Print["simplify"];*)
					LenDenNum=Min[IntegerLength[Denominator[x1[[i]]]],IntegerLength[Abs[Numerator[x1[[i]]]]]];
					x1[[i]]=IntegerPart[Numerator[x1[[i]]]/10^(LenDenNum-2)]/IntegerPart[Denominator[x1[[i]]]/10^(LenDenNum-2)];
				];
				If[IntegerLength[Denominator[x1[[i]]]]>5,x1[[i]]=0;];
				++i;
			];
			(*Print["celljump direction 1 - simplify: ",isDir,x1];*)
			If[isDir&&Not[MemberQ[cycle,x1]], AppendTo[cycle,x1]; x = x1,
				(*Print["cntLS=",cntLS," maxCntLS=",maxCntLS];*)
				If[cntLS>maxCntLS,
		            cad=GenericCylindricalDecomposition[And@@Table[Or@@Table[If[cnf[[i,j,2]]<0,polyList[[cnf[[i,j,1]]]]<0,polyList[[cnf[[i,j,1]]]]>0],{j,Length[cnf[[i]]]}],{i,Length[cnf]}],varList];
                    If[cad=={False,False},
                        Return[{"unsat","openCAD"}],
                        (*Return[{"CAD: sat",FindInstance[cad[[1]],varList]}];*)
                        Return[{"sat","openCAD"}];
                    ];
                ];
                ++cntLS;
                (*Print["cntLS: ",cntLS];*)
                (*Print["celljump axis 2"];*)
				{isAxis, x1} = SearchAndApplyOp2[polyList, cnf, varList, x, w]; (* \:6cbf\:5750\:6807\:8f74celljump 2 *)
				(*Print["celljump axis 2: ",isAxis,x2];*)
				x2=x;
				If[Length[varList2]>=2,
					x2[varList2[[1]]]=x1[varList2[[1]]];
					x2[varList2[[2]]]=x1[varList2[[2]]],
					x2[varList2[[1]]]=x1[varList2[[1]]];
				];
				i=1;
				While[i<=varnum,
					If[Max[IntegerLength[Denominator[x2[[i]]]],IntegerLength[Abs[Numerator[x2[[i]]]]]]>5,
						(*Print["simplify"];*)
						LenDenNum=Min[IntegerLength[Denominator[x2[[i]]]],IntegerLength[Abs[Numerator[x2[[i]]]]]];
						x2[[i]]=IntegerPart[Numerator[x2[[i]]]/10^(LenDenNum-2)]/IntegerPart[Denominator[x2[[i]]]/10^(LenDenNum-2)];
					];
					If[IntegerLength[Denominator[x2[[i]]]]>5,x2[[i]]=0;];
					++i;
				];
				(*Print["celljump axis 2 - simplify: ",isAxis,x2];*)
				If[isAxis&&Not[MemberQ[cycle,x2]], 
				    AppendTo[cycle,x2]; x = x2, 
				    (*Print["cycle: ",cycle];*)
				    (*Print["mcsat: ",{clauses,mcsatPoly,varListLast}];*)
				    (*Print["mcsatPoly: ",mcsatPoly];*)
		            (*Print["mcsat: ",{clauses,mcsatPoly,varListLast}];*)
		            (*If[MCSATSolver[clauses,mcsatPoly,varListLast][[1]]=="sat",Return[{"sat","ELS-mcsat"}]],*)
		        
		            (*If[MCSATSolver[clauses,Table[If[Length[Variables[mcsatPoly[[i]]]]==0,varListLast[[1]],mcsatPoly[[i]]],{i,Length[mcsatPoly]}],varListLast][[1]]=="sat",Return[{"sat","exLS-mcsat"}]],*)

		            (*Print["cntLS=",cntLS," maxCntLS=",maxCntLS];*)
					If[cntLS>maxCntLS,
					    (*Print[{And@@Table[Or@@Table[If[cnf0[[i,j,2]]<0,polyList0[[cnf0[[i,j,1]]]]<0,polyList0[[cnf0[[i,j,1]]]]>0],{j,Length[cnf0[[i]]]}],{i,Length[cnf0]}],varList}];*)
                        cad=GenericCylindricalDecomposition[And@@Table[Or@@Table[If[cnf[[i,j,2]]<0,polyList[[cnf[[i,j,1]]]]<0,polyList[[cnf[[i,j,1]]]]>0],{j,Length[cnf[[i]]]}],{i,Length[cnf]}],varList];
                        If[cad=={False,False},
                            Return[{"unsat","openCAD"}],
                            (*Return[{"CAD: sat",FindInstance[cad[[1]],varList]}];*)
                            Return[{"sat","openCAD"}];
                        ];
                    ];
                    ++cntLS;
                    (*Print["cntLS: ",cntLS];*)
                    (*Print["cntLS: ",cntLS];*)
				    w = UpdateWeight[polyList, cnf, varList2, x, w];
                    {isDir, x1} = GradSearchAndApplyOp2[polyList, cnf, varList, x, w]; (* \:6cbf\:67d0\:4e9b\:65b9\:5411celljump 2 *)
					(*Print["celljump direction 2: ",isDir,x2];*)
					x2=x;
				    If[Length[varList2]>=2,
						x2[varList2[[1]]]=x1[varList2[[1]]];
						x2[varList2[[2]]]=x1[varList2[[2]]],
						x2[varList2[[1]]]=x1[varList2[[1]]];
					];
					i=1;
					While[i<=varnum,
						If[Max[IntegerLength[Denominator[x2[[i]]]],IntegerLength[Abs[Numerator[x2[[i]]]]]]>5,
							(*Print["simplify"];*)
							LenDenNum=Min[IntegerLength[Denominator[x2[[i]]]],IntegerLength[Abs[Numerator[x2[[i]]]]]];
							x2[[i]]=IntegerPart[Numerator[x2[[i]]]/10^(LenDenNum-2)]/IntegerPart[Denominator[x2[[i]]]/10^(LenDenNum-2)];
						];
						If[IntegerLength[Denominator[x2[[i]]]]>5,x2[[i]]=0;];
						++i;
					];
					(*Print["celljump direction 2 - simplify: ",isDir,x2];*)
				    If[MemberQ[cycle,x2],(*Print["cycle"];*)Break[]];
				    If[isDir,AppendTo[cycle,x2]; x = x2,
				        (*Print["cycle: ",cycle];*)
						(*mcsatPoly=polyList/.x;*)
		                (*Print["mcsat: ",{clauses,mcsatPoly,varListLast}];*)
		                (*If[MCSATSolver[clauses,mcsatPoly,varListLast][[1]]=="sat",Return[{"sat","exLS-mcsat"}]],*)
				        Break[];
					];
				];
			];
		];
	];
	Return[{"unknown","ELS",cntLS}];
];


(* ::Subsubsection:: *)
(*LSSolver*)
(*\:529f\:80fd\:ff1a\:6c42\:89e3SMT\:7684\:5c40\:90e8\:641c\:7d22\:6c42\:89e3\:5668\:ff0c\:4e24\:7ea7\:7b56\:7565\:662fLS\:7684celljump*)


LSSolver[polyList0_, cnf0_, varList_,lsLimit_,cntLS0_,maxCntLS_]:=
Module[{cnt=1,init,lsInit={},ans,cons,consZero,polyList,cnf,LenDenNum,
		lnum,varnum,deg(*,cntELS,maxCntELS*),cntLS=cntLS0},
	
	(*\:5904\:7406\:591a\:9879\:5f0f\:6052\:7b49\:4e8e\:5e38\:6570\:7684\:60c5\:5f62*)            
	cons=Union[Map[{#, -1} &,Select[Range[Length[polyList0]],Length[Variables[polyList0[[#]]]]==0&&polyList0[[#]]<0&]],Map[{#, 1} &, Select[Range[Length[polyList0]],Length[Variables[polyList0[[#]]]]==0&&polyList0[[#]]>0&]]];
	consZero=Select[Range[Length[polyList0]],Length[Variables[polyList0[[#]]]]==0&&polyList0[[#]]==0&];
	(*Print[cons];*)
	cnf=Table[If[Intersection[cons,cnf0[[i]]]=={},cnf0[[i]],Nothing],{i,Length[cnf0]}]/.Table[Table[{cons[[i,1]],-cons[[i,2]]},{i,Length[cons]}][[i]]->Nothing,{i,Length[cons]}](*/.{}->Nothing*)/.Table[Table[{consZero[[i]],1},{i,Length[consZero]}][[i]]->Nothing,{i,Length[consZero]}]/.Table[Table[{consZero[[i]],-1},{i,Length[consZero]}][[i]]->Nothing,{i,Length[consZero]}];
	If[MemberQ[cnf,{}]||cnf=={},Return[{"unsat","There are constants that cannot be satisfied."}]];
	polyList=ReplacePart[polyList0, Table[Abs[cons[[i,1]]]->varList[[1]],{i,Length[cons]}]];
	polyList=ReplacePart[polyList, Table[consZero[[i]]->varList[[1]],{i,Length[consZero]}]];
	(*Print["cnf: ",cnf];
	Print["polyList: ",polyList];*)
	
	While[cnt<=lsLimit,
		Which[cnt==1,
			(*Print["ELS start: ",cnt];*)
			init=Association[Map[#->1&,varList]];
			AppendTo[lsInit,init];
			ans=LS[init,polyList,cnf,varList,cntLS,maxCntLS];
            If[ans[[1]]!="unknown",Return[ans],cntLS=ans[[3]];];
			++cnt,
			cnt>=2&&cnt<=6,
			(*Print["ELS start: ",cnt];*)
			init=Association[Map[#->RandomChoice[{-1,1}]&,varList]];
			If[Not[MemberQ[lsInit,init]],
                AppendTo[lsInit,init];
                ans=LS[init,polyList,cnf,varList,cntLS,maxCntLS];
                If[ans[[1]]!="unknown",Return[ans],cntLS=ans[[3]];];
            ];
            ++cnt,
            cnt>=7,
            (*Print["ELS start: ",cnt];*)
            init=Association[Map[#->RandomInteger[{-50*(cnt-6),50*(cnt-6)}]&,varList]];
            If[Not[MemberQ[lsInit,init]],
                AppendTo[lsInit,init];
                ans=LS[init,polyList,cnf,varList,cntLS,maxCntLS];
                If[ans[[1]]!="unknown",Return[ans],cntLS=ans[[3]];];
            ];
            ++cnt;
		];
	];
	Return[{"unknown","LS",cntLS}];
];


LS[x0_, polyList_, cnf_, varList_,cntLS0_,maxCntLS_]:=
Module[{i, x, w, isAxis, x1, x2, isDir,
		cnt=1,init,lsInit={},(*maxCntLS,*)varListLast,vars=Length[varList],varList2,
		clauses,y,cons,consZero,cycle={},cad,mcsatPoly,LenDenNum,cntLS=cntLS0,varnum=Length[varList]},
	
	clauses=Table[Table[cnf[[i,j,1]]*cnf[[i,j,2]],{j,Length[cnf[[i]]]}],{i,Length[cnf]}];
	
	(*maxCntLS=2*Min[Length[polyList],Max[Exponent[(MonomialList[polyList]/.Association[Map[#->y&,varList]]),y]]]*vars;*)
	(*Print["maxCntLS: ",maxCntLS];*)
	x = x0;
	w = Association[Table[cnf[[i]] -> 1, {i, Length[cnf]}]];
	(*Print["initial x: ", x];*)
	
	While[True,
		If[SatCheck[polyList, cnf, varList, x],Return[{"sat","LS"}]];
		x1=x;
		(*Print[mcsatPoly];*)
		(*Print["cntLS=",cntLS," maxCntLS=",maxCntLS];*)
		If[cntLS>maxCntLS,
		    cad=GenericCylindricalDecomposition[And@@Table[Or@@Table[If[cnf[[i,j,2]]<0,polyList[[cnf[[i,j,1]]]]<0,polyList[[cnf[[i,j,1]]]]>0],{j,Length[cnf[[i]]]}],{i,Length[cnf]}],varList];
            If[cad=={False,False},
                Return[{"unsat","openCAD"}],
                (*Return[{"CAD: sat",FindInstance[cad[[1]],varList]}];*)
                Return[{"sat","openCAD"}];
            ];
        ];
        ++cntLS;
        (*Print["cntLS: ",cntLS];*)
		{isAxis, x1} = SearchAndApplyOp1[polyList, cnf, varList, x, w]; (* \:6cbf\:5750\:6807\:8f74celljump 1 *)
		(*Print["celljump axis 1: ",isAxis,x1];*)
		(*If[Max[Denominator[Values[x1]]]>10||Max[Abs[Numerator[Values[x1]]]]>10,Break[]];*)
		i=1;
		While[i<=varnum,
			If[Max[IntegerLength[Denominator[x1[[i]]]],IntegerLength[Abs[Numerator[x1[[i]]]]]]>5,
				(*Print["simplify"];*)
				LenDenNum=Min[IntegerLength[Denominator[x1[[i]]]],IntegerLength[Abs[Numerator[x1[[i]]]]]];
				x1[[i]]=IntegerPart[Numerator[x1[[i]]]/10^(LenDenNum-2)]/IntegerPart[Denominator[x1[[i]]]/10^(LenDenNum-2)];
			];
			If[IntegerLength[Denominator[x1[[i]]]]>5,x1[[i]]=0;];
			++i;
		];
		(*Print["celljump axis 1 - simplify: ",isAxis,x1];*)
		If[isAxis&&Not[MemberQ[cycle,x1]], AppendTo[cycle,x1]; x = x1,
			w = UpdateWeight[polyList, cnf, varList, x, w];
			(*Print["cntLS=",cntLS," maxCntLS=",maxCntLS];*)
			If[cntLS>maxCntLS,
		        cad=GenericCylindricalDecomposition[And@@Table[Or@@Table[If[cnf[[i,j,2]]<0,polyList[[cnf[[i,j,1]]]]<0,polyList[[cnf[[i,j,1]]]]>0],{j,Length[cnf[[i]]]}],{i,Length[cnf]}],varList];
                If[cad=={False,False},
                    Return[{"unsat","openCAD"}],
                    (*Return[{"CAD: sat",FindInstance[cad[[1]],varList]}];*)
                    Return[{"sat","openCAD"}];
                ];
            ];
            ++cntLS;
            (*Print["cntLS: ",cntLS];*)
			{isDir, x1} = GradSearchAndApplyOp1[polyList, cnf, varList, x, w]; (* \:6cbf\:67d0\:4e9b\:65b9\:5411celljump 1 *)
			(*If[Max[Denominator[Values[x1]]]>10^20||Max[Abs[Numerator[Values[x1]]]]>10^20,Break[]];*)
			(*Print["celljump direction 1: ",isDir,x1];*)
			(*Print["Denominator Length: ",IntegerLength[Denominator[x1[[1]]]]];*)
			i=1;
			While[i<=varnum,
				If[Max[IntegerLength[Denominator[x1[[i]]]],IntegerLength[Abs[Numerator[x1[[i]]]]]]>5,
					(*Print["simplify"];*)
					LenDenNum=Min[IntegerLength[Denominator[x1[[i]]]],IntegerLength[Abs[Numerator[x1[[i]]]]]];
					x1[[i]]=IntegerPart[Numerator[x1[[i]]]/10^(LenDenNum-2)]/IntegerPart[Denominator[x1[[i]]]/10^(LenDenNum-2)];
				];
				If[IntegerLength[Denominator[x1[[i]]]]>5,x1[[i]]=0;];
				++i;
			];
			(*Print["celljump direction 1 - simplify: ",isDir,x1];*)
			If[MemberQ[cycle,x1],(*Print["cycle"];*)Break[]];
			If[isDir&&Not[MemberQ[cycle,x1]], AppendTo[cycle,x1]; x = x1,
				(*Print["cntLS=",cntLS," maxCntLS=",maxCntLS];*)
				If[cntLS>maxCntLS,
		            cad=GenericCylindricalDecomposition[And@@Table[Or@@Table[If[cnf[[i,j,2]]<0,polyList[[cnf[[i,j,1]]]]<0,polyList[[cnf[[i,j,1]]]]>0],{j,Length[cnf[[i]]]}],{i,Length[cnf]}],varList];
                    If[cad=={False,False},
                        Return[{"unsat","openCAD"}],
                        (*Return[{"CAD: sat",FindInstance[cad[[1]],varList]}];*)
                        Return[{"sat","openCAD"}];
                    ];
                ];
                ++cntLS;
                Break[];
			];
		];
	];
	Return[{"unknown","LS",cntLS}];
];


(* ::Subsubsection:: *)
(*MCSATSolver*)
(*\:529f\:80fd\:ff1a\:6c42\:89e3SMT\:7684MCSAT\:6c42\:89e3\:5668*)


MCSATSolver[Clause0_,F2_,X_]:=Module[{a,cc,i,j,xmap=<||>,fmap=<||>,F1,F,Flevel,Fnow,conflictstatelist,Ci,Cli,Clause,Clause1,Clearn={},
                varnum,Clausenum,assignment=Association[Map[#->0&,X]],lorder,z,lnum,ML,M,Morder,VC,
                Cstatus,Clstatus,levell,levelc,levelcl,level,tmplevel,tmpc,tmpcl,status,nowc,conflict,
                getFnow,getFlevel,getClause,checkconflict,Polynomialroot,getorder,addl,getF,
                samplecell,getsamplecell,nextsamplecell,cons,consZero},
    
    (*Print["MCSATSolver: ",{Clause0,F2,X}];*)
    (*\:5904\:7406\:591a\:9879\:5f0f\:6052\:7b49\:4e8e\:5e38\:6570\:7684\:60c5\:5f62*)            
	cons=Union[-1*Select[Range[Length[F2]],Length[Variables[F2[[#]]]]==0&&F2[[#]]<0&],Select[Range[Length[F2]],Length[Variables[F2[[#]]]]==0&&F2[[#]]>0&]];
	consZero=Select[Range[Length[F2]],Length[Variables[F2[[#]]]]==0&&F2[[#]]==0&];
	(*Print[cons];*)
	Clause1=Table[If[Intersection[cons,Clause0[[i]]]=={},Clause0[[i]],Nothing],{i,Length[Clause0]}]/.Table[-cons[[i]]->Nothing,{i,Length[cons]}](*/.{}->Nothing*)/.Table[consZero[[i]]->Nothing,{i,Length[consZero]}]/.Table[-consZero[[i]]->Nothing,{i,Length[consZero]}];
	If[MemberQ[Clause1,{}]||Clause1=={},Return[{"unsat","There are constants that cannot be satisfied."}]];
	Clause=Clause1;
	F1=ReplacePart[F2, Table[Abs[cons[[i]]]->X[[1]],{i,Length[cons]}]];
	F1=ReplacePart[F1, Table[consZero[[i]]->X[[1]],{i,Length[consZero]}]];
	F=Map[{1,#}&,F1];	
	(*Print["Clause: ",Clause1];*)
	(*Print["F: ",F1];*)
                
    (*Print[F];*)
    lnum=Length[F];
    (*Symmetry Check*)
    Module[{x0=X[[1]],C={}},
    Scan[
        If[(F1/.{#->x0,x0->#})==F1,AppendTo[F,{1,#-x0}];++lnum;AppendTo[C,{-lnum}];x0=#]&
    ,X[[2;;]]];
    (*Ding: Print*)
    (*Print["F (sym): ",F];*)
    (*Print[F];Print[Clause]*)
    If[Length[C]>Length[X]/2,(*Print["Find Symmetry: ",Map[Sequence@@F[[Abs[#],2]]&,C]];*)Clause={Sequence@@C,Sequence@@Clause}]
    ];
    (**)
    varnum=Length[X];
    Clausenum=Length[Clause];
    
    Scan[(xmap[X[[#]]]=# )&,Range[varnum]];
    Scan[(fmap[F[[#]]]=# )&,Range[lnum]];
    getorder=Function[l,
        Switch[l[[1]],
            1,Max[Map[xmap[#]&,Variables[l[[2]]]]],
            2,Max[Map[xmap[#]&,Variables[l[[2]]]]],
            3,xmap[l[[4]]],
            4,xmap[l[[4]]],
            5,Length[l[[3]]]
        ]
    ];
    Ci=Table[{},varnum];
    Cli=Table[{},varnum];
    levell=Table[{},varnum];
    conflictstatelist=Table[{},varnum];
    (* lorder=Table[If[Length[F[[i]]]>1,xmap[F[[i,3]]],Max[Map[xmap[#]&,Variables[F[[i,1]]]]]],{i,1,lnum}]; *)
     lorder=Map[Max[Map[xmap[#]&,Variables[#[[2]]]]]&,F];
    Scan[AppendTo[Ci[[Max[Map[lorder[[Abs[#]]]&,Clause[[#]]]]]],#]&,Range[Clausenum]];
    (* Ding: Scan[AppendTo[levell[[lorder[[#]]]],#]&,Range[1,lnum]];*)
    Scan[AppendTo[levell[[lorder[[#]]]],#]&,Range[lnum]];
    Flevel=Table[0,lnum];
    Fnow=Table[0,lnum];VC={Table[{},lnum],Table[{},lnum]};
    Cstatus=Table[{0,0},Clausenum];Clstatus={};
    level=1;
    ML=Table[{},varnum];
    Morder=Table[0,lnum];M=Table[0,lnum];
    levelc=Table[{},varnum];levelcl=Table[{},varnum];
    conflictstatelist[[level]]={};
    (* Scan[If[Length[F[[#]]]>1,Flevel[[#]]=Polynomialroot[F[[#,1]]/.assignment,Abs[F[[#,2]]]],Flevel[[#]]=F[[#,1]]/.assignment]&,levell[[level]]];     *)
    (* Ding: Scan[(Flevel[[#]]=F[[#,2]]/.(X[[1]]->z))&,levell[[level]]];*)
    Scan[(Flevel[[#]]=F1[[#]]/.(X[[1]]->z))&,levell[[level]]];
    (* levelc[[level]]=Select[ Map[{Select[Clause[[#]],lorder[[Abs[#]]]==level& ],#}&,Ci[[level]]], Not[MemberQ[Map[Fnow[[#]]&,Select[Clause[[#[[2]]]],lorder[[Abs[#]]]<level&]],True]]& ]; *)
    levelc[[level]]=Map[{Clause[[#]],#}&,Ci[[level]]];
    (* Ding: Scan[(VC[[1]][[#]]={};VC[[-1]][[#]]={})&,levell[[level]] ];*)
    For[i=1,i<=Length[levelc[[level]]],++i,
        Scan[AppendTo[VC[[Sign[#],Abs[#]]], levelc[[level,i,2]] ]&,levelc[[level,i,1]]];
        Cstatus[[levelc[[level,i,2]]]]={Length[levelc[[level,i,1]]],0}
    ];
    Polynomialroot[F_,Index_]:=If[Index>CountRoots[F,z],Infinity,Root[F,Index]];
    getsamplecell=Function[{l,a},
        Module[{newl},
            If[Length[a]!=0,
                newl=getF[{5,l,a}];
                ,newl=Nothing];
            newl]];
    nextsamplecell=Function[{lst,a,x0},
        Module[{pc=GetSampleInterval[lst,a,x0],nextl,fg,fl},
            nextl={getsamplecell[pc[[2]],a[[;;-2]]]};
            Scan[(
                    fg=getF[{3,#[[2]]/.(x0->z),#[[3]],x0}];
                    fl=getF[{4,#[[2]]/.(x0->z),#[[3]],x0}];
                    Switch[#[[1]],
                        Greater,AppendTo[nextl,-fg],
                        Equal,AppendTo[nextl,fg];AppendTo[nextl,fl],
                        Less,AppendTo[nextl,-fl]]
                )&,pc[[1]]]; 
            nextl
        ]
    ];
    samplecell=Function[i,If[F[[i,1]]==5 && SameQ[F[[i,4]],False],
        Module[{newlist=If[Length[F[[i,2]]]==1,
                            Pmc[F[[i,2,1]],assignment,X[[lorder[[i]]+1]]],
                            Ps[F[[i,2]],F[[i,3]],X[[lorder[[i]]+1]]]],
                x0=X[[lorder[[i]]]]},
                F[[i,4]]=nextsamplecell[newlist,F[[i,3]],x0];
                (*Ding: Print*)
                (*Print["F (sample-cell): ",F];*)
        ]]];

    getFnow=(Switch[F[[#,1]],
        1,(F[[#,2]]/.assignment)>0,
        2,(F[[#,2]]/.assignment)==0,
        3,assignment[[lorder[[#]]]]>Flevel[[#]],
        4,assignment[[lorder[[#]]]]<Flevel[[#]],
        5,If[assignment[[;;lorder[[#]]]]==F[[#,3]],
            False,
            samplecell[#];
            MemberQ[Map[
              (*  If[F[[Abs[#],1]]==5,
                    !Xor[Fnow[[Abs[#]]],#>0],
                    !Xor[getFnow[Abs[#]],#>0]]&*)
                    (!Xor[Fnow[[Abs[#]]],#>0])&
                    ,F[[#,4]]],True]]
    ])&;
    getFlevel=(Switch[F[[#,1]],
        1,F[[#,2]]/.(X[[level]]->z)/.assignment,
        2,F[[#,2]]/.(X[[level]]->z)/.assignment,
        3,Polynomialroot[F[[#,2]]/.assignment,F[[#,3]]],
        4,Polynomialroot[F[[#,2]]/.assignment,F[[#,3]]],
        _,False
    ])&;
    getClause=Function[{c,l},
        Select[
            Map[{Map[
                    If[lorder[[Abs[#]]]==level,#,
                        !Xor[Fnow[[Abs[#]]],#>0]]&
                ,c[[#]]]/.(False->Nothing),#}&,l],
            Not[MemberQ[#[[1]],True]]&]
    ];
    checkconflict=Function[{list,index},
        Switch[F[[Abs[index],1]],
            1,CheckConflictHalf[list,Flevel[[Abs[index]]],z,index,index>0,False],
            3,CheckConflictHalf[list,Flevel[[Abs[index]]],index,index>0,False],
            4,CheckConflictHalf[list,Flevel[[Abs[index]]],index,index<0,False]]
    ];
    getF=Function[l,
        Module[{ans=fmap[l]},
            If[SameQ[Head[ans],Missing],
                AppendTo[F,l];++lnum;ans=lnum;fmap[l]=lnum;
                If[l[[1]]==5,AppendTo[F[[ans]],False]];
                AppendTo[lorder,getorder[l]];
                AppendTo[levell[[lorder[[ans]]]],lnum];AppendTo[Flevel,0];
                AppendTo[Fnow,0];AppendTo[M,0];
                AppendTo[Morder,0];AppendTo[VC[[1]],{}];AppendTo[VC[[-1]],{}];
                Flevel[[ans]]=getFlevel[ans];
                If[level>lorder[[ans]],Fnow[[ans]]=getFnow[ans]];
                (*Ding: Print*)
                (*Print["F (getF): ",F];*)
            ];
            ans
        ]
    ];
    addl=Function[l,
        Module[{index=l[[1]]},
            M[[Abs[index]]]=Sign[index];AppendTo[ML[[level]],l];Morder[[Abs[index]]]=Length[ML[[level]]];
            Scan[If[#>0,++Cstatus[[#,2]];--Cstatus[[#,1]],++Clstatus[[-#,2]];--Clstatus[[-#,1]]]&,VC[[Sign[index],Abs[index]]]];
            Scan[If[#>0,--Cstatus[[#,1]],--Clstatus[[-#,1]]]&,VC[[-Sign[index],Abs[index]]]];
        ]
    ];
    
    While[True,
		tmpc=MinimalBy[Select[Range[Length[levelc[[level]]]],Cstatus[[levelc[[level,#,2]],2]]==0&],Cstatus[[levelc[[level,#,2]],1]]&];
        tmpcl=MinimalBy[Select[Range[Length[levelcl[[level]]]],Clstatus[[levelcl[[level,#,2]],2]]==0&],Clstatus[[levelcl[[level,#,2]],1]]&];
        (*Print["assignment: ",assignment];*)
        If[Length[tmpc]==0 && Length[tmpcl]==0,
            assignment[X[[level]]]=FindMid[conflictstatelist[[level]]];
            (*Ding: Print*)
            (*Print["mcsat: ", assignment];*)
            (* Scan[If[M[[#]]!=0,Fnow[[#]]=M[[#]]>0,If[Length[F[[#]]]>1,If[F[[#,2]]>0,Fnow[[#]]=assignment[X[[level]]]>Flevel[[#]],Fnow[[#]]=assignment[X[[level]]]<Flevel[[#]]],Fnow[[#]]=((F[[#,1]]/.assignment)>0)]]&,levell[[level]]]; *)
            Scan[If[M[[#]]!=0,Fnow[[#]]=M[[#]]>0,If[F[[#,1]]!=5,Fnow[[#]]=getFnow[#]]]&,levell[[level]]];
            Scan[If[M[[#]]==0 && F[[#,1]]==5,Fnow[[#]]=getFnow[#]]&,levell[[level]]];
            
            ++level;(*maxlevel=Max[level,maxlevel];*)
            If[level>varnum,(*Return[{"sat",assignment}]*)Return[{"sat","mcsat",assignment}]];
            conflictstatelist[[level]]={};
            Scan[(M[[#]]=0)&,levell[[level]]];ML[[level]]={};
            (* Scan[If[Length[F[[#]]]>1,Flevel[[#]]=Polynomialroot[F[[#,1]]/.assignment,Abs[F[[#,2]]]],Flevel[[#]]=F[[#,1]]/.assignment]&,levell[[level]]];     *)
            Scan[(Flevel[[#]]=getFlevel[#])&,levell[[level]]];
            (* levelc[[level]]=Select[ Map[{Select[Clause[[#]],lorder[[Abs[#]]]==level& ],#}&,Ci[[level]]], Not[MemberQ[Map[Fnow[[#]]&,Select[Clause[[#[[2]]]],lorder[[Abs[#]]]<level&]],True]]& ];
            levelcl[[level]]=Select[ Map[{Select[Clearn[[#]],lorder[[Abs[#]]]==level& ],#}&,Cli[[level]]], Not[MemberQ[Map[Fnow[[#]]&,Select[Clearn[[#[[2]]]],lorder[[Abs[#]]]<level&]],True]]& ]; *)
            levelc[[level]]=getClause[Clause,Ci[[level]]];
            levelcl[[level]]=getClause[Clearn,Cli[[level]]];
            Scan[(VC[[1,#]]={};VC[[-1,#]]={})&,levell[[level]] ];
            For[i=1,i<=Length[levelc[[level]]],++i,
                Scan[AppendTo[VC[[Sign[#],Abs[#]]], levelc[[level,i,2]] ]&,levelc[[level,i,1]]];
                Cstatus[[levelc[[level,i,2]]]]={Length[levelc[[level,i,1]]],0}
            ];
            For[i=1,i<=Length[levelcl[[level]]],++i,
                Scan[AppendTo[VC[[Sign[#],Abs[#]]], -levelcl[[level,i,2]] ]&,levelcl[[level,i,1]]];
                Clstatus[[levelcl[[level,i,2]]]]={Length[levelcl[[level,i,1]]],0}
            ];
        ,
            status=-1;
            If[Length[tmpc]>0,
                If[Cstatus[[levelc[[level,tmpc[[1]],2]],1]]==0,status=0;nowc=tmpc[[1]],
                    If[Cstatus[[levelc[[level,tmpc[[1]],2]],1]]==1,status=1;nowc=tmpc[[1]],status=2;nowc=tmpc[[1]]]]
            ];
            If[status!=0 && Length[tmpcl]>0,
                If[Clstatus[[levelcl[[level,tmpcl[[1]],2]],1]]==0,status=0;nowc=-tmpcl[[1]],
                    If[Clstatus[[levelcl[[level,tmpcl[[1]],2]],1]]==1 && status!=1,status=1;nowc=-tmpcl[[1]]];
                    If[status==-1,status=2;nowc=-tmpcl[[1]]]
                ]
            ];
            
            If[status==0,
                If[nowc>0,conflict=Clause[[levelc[[level,nowc,2]]]],conflict=Clearn[[levelcl[[level,-nowc,2]]]]];
                (*Ding: Print*)
                (*Print["conflict: ",conflict];*)
                While[status==0,
                    For[a = Select[conflict, lorder[[Abs[#]]]==level && M[[Abs[#]]]!=0 && Length[ML[[level,Morder[[Abs[#]]]]]] == 2 &],Length[a] != 0, 
                               a = Select[conflict, lorder[[Abs[#]]]==level && M[[Abs[#]]]!=0 && Length[ML[[level,Morder[[Abs[#]]]]]] == 2 &],
                        conflict = Fold[ClauseResolve[#1, ML[[level,Morder[[Abs[#2]]],2]], #2] &, conflict, a];
                    ];
                    (*Ding: Print*)
                    (*Print["conflict: ",conflict];*)
                    If[Length[conflict]==0,Return[{"unsat","mcsat"}]];                    
                    
                    tmplevel=Max[Map[lorder[[Abs[#]]]&,conflict]];
                    
                    If[tmplevel==level,
                        a=Select[conflict,(lorder[[Abs[#]]]==level && F[[Abs[#],1]]==5)&];
                        If[Length[a]!=0,
                            (* Scan[samplecell[#]&,a];
                            If[Length[a]==1 || level==1,
                                conflict=DeleteDuplicates[
                                Fold[(If[#2<0,Print["error:",  #, " in conflict ."]];
                                #1/.(#2->Sequence@@F[[#2,4]]))&
                                ,conflict,a]]; 
                            ,
                                Module[{c=<||>},
                                    conflict=Select[conflict,(lorder[[Abs[#]]]!=level || F[[Abs[#],1]]!=5)&];
                                    Scan[If[SameQ[Head[c[F[[#,3]]]],Missing],c[F[[#,3]]]={#},AppendTo[c[F[[#,3]]],#]]&,a];
                                    c=List@@c;
                                    c=Map[nextsamplecell[DeleteDuplicates[Flatten[Map[(F[[F[[#,4,1]],2]])&,#]]],F[[#[[1]],3]],X[[level]]]&,c];
                                    conflict=DeleteDuplicates[Flatten[{conflict,c}]];
                                ];
                            ]; *)
                            conflict=DeleteDuplicates[
                                Fold[(If[#2<0,Print["error:",  #, " in conflict ."]];
                                samplecell[#2];#1/.(#2->Sequence@@F[[#2,4]]))&
                                ,conflict,a]];
                            (*Ding: Print*)
                            (*Print["conflict: ",conflict];*)
                            tmplevel=Max[Map[lorder[[Abs[#]]]&,conflict]];
                            ,
                            AppendTo[Clearn,conflict];
                            (*Ding: Print*)
                            (*Print["Clearn: ",Clearn];*)
                            AppendTo[Cli[[level]],Length[Clearn]];
                            Scan[AppendTo[VC[[Sign[#],Abs[#] ]],-Length[Clearn]]&, Select[conflict,lorder[[Abs[#]]]==level& ] ];
                            a=Select[conflict,lorder[[Abs[#]]]==level&];
                            AppendTo[levelcl[[level]],{a,Length[Clearn]}];
                            AppendTo[Clstatus,{Length[Select[a,M[[Abs[#]]]==0&]],0}];
                            If[Clstatus[[-1,1]]<2,status=1,status=2];
                            nowc=-Length[levelcl[[level]]];
                            If[Clstatus[[-1,1]]==0,
                                If[Length[a]==1,a=Max[Map[Morder[[Abs[#]]]&,a]]-1,
                                    a=RankedMax[Map[Morder[[Abs[#]]]&,a],2]];
                                Scan[
                                    (M[[Abs[#[[1]]]]]=0;
                                    Scan[If[#>0,--Cstatus[[#,2]];++Cstatus[[#,1]],--Clstatus[[-#,2]];++Clstatus[[-#,1]]]&,VC[[Sign[#[[1]]],Abs[#[[1]]]]]];
                                    Scan[If[#>0,++Cstatus[[#,1]],++Clstatus[[-#,1]]]&,VC[[-Sign[#[[1]]],Abs[#[[1]]]]]];)&
                                ,ML[[level,a+1;;]]];
                                ML[[level]]=ML[[level,;;a]];
                                (* conflictstatelist[[level]]=Fold[
                                    If[Length[F[[Abs[#2[[1]]]]]]==1,
                                    CheckConflictHalf[#1,Flevel[[Abs[#2[[1]]]]],X[[level]],#2[[1]],#2[[1]]>0,False][[2]],
                                    CheckConflictHalf[#1,Flevel[[Abs[#2[[1]]]]],#2[[1]],!Xor[F[[Abs[#2[[1]]],2]]>0,#2[[1]]>0],False][[2]]]&
                                ,{},ML[[level]]]]; *)
                                conflictstatelist[[level]]=Fold[checkconflict[#1,#2[[1]]][[2]]&,{},ML[[level]]]]]];
                    level=tmplevel;
                ]
            ];
            
            If[nowc>0,cc=levelc[[level,nowc,1]],cc=levelcl[[level,-nowc,1]]];
            If[status==1,
                a=Select[cc,M[[Abs[#]]]==0&][[1]];
            ,
                a=MaximalBy[Select[cc,M[[Abs[#]]]==0&],Length[Select[VC[[Sign[#],Abs[#]]],If[#<0,Clstatus[[-#,2]]==0,Cstatus[[#,2]]==0]&]]&][[1]];
            ];
            (* If[Length[F[[Abs[a]]]]==1,
                tmpc=CheckConflictHalf[conflictstatelist[[level]],Flevel[[Abs[a]]],X[[level]],a,a>0,False];
            ,
                tmpc=CheckConflictHalf[conflictstatelist[[level]],Flevel[[Abs[a]]],a,!Xor[F[[Abs[a],2]]>0,a>0],False];
            ]; *)
            tmpc=checkconflict[conflictstatelist[[level]],a];
            If[tmpc[[1]],
                conflictstatelist[[level]]=tmpc[[2]];
                If[nowc>0,cc=Clause[[levelc[[level,nowc,2]]]],cc=Clearn[[levelcl[[level,-nowc,2]]]]];
            ,
                cc=DeleteDuplicates[Map[#[[4]]&,tmpc[[2]]]];
                If[level>1,
                    Module[{l},
                        l=Map[Function[x,
                                If[F[[Abs[x],1]]==1 || F[[Abs[x],1]]==2,
                                    F[[Abs[x],2]],
                                    F[[Abs[x],2]]/.(z->X[[level]])]]
                            ,cc];
                        l=Select[DeleteDuplicates[Flatten[Map[FactorList,l][[All,All,1]]]],UnsameQ[Variables[#],{}]&];
                        conflict=getsamplecell[{l},assignment[[;;level-1]]];
                        (*Ding: Print*)
                        (*Print["conflict: ",conflict];*)
                    ]
                    ,
                    conflict=Nothing;
                    (*Ding: Print*)
                     (*Print["conflict: ",conflict];*)
                ];
                (* cc=Flatten[{conflict,Map[Minus,cc]}];  *)
                cc={Sequence@@Map[Minus,cc],conflict};
                a=-a;
                status=1;
            ];
            If[status==1,addl[{a,cc}],addl[{a}]];
            (* M[[Abs[a]]]=Sign[a];
            If[status==1,AppendTo[ML[[level]],{a,cc}],AppendTo[ML[[level]],{a}]];
            Morder[[Abs[a]]]=Length[ML[[level]]];
            Scan[If[#>0,++Cstatus[[#,2]];--Cstatus[[#,1]],++Clstatus[[-#,2]];--Clstatus[[-#,1]]]&,VC[[Sign[a],Abs[a]]]];
            Scan[If[#>0,--Cstatus[[#,1]],--Clstatus[[-#,1]]]&,VC[[-Sign[a],Abs[a]]]]; *)
            (* Theoretical reasoning *)
            (* If[Length[F[[Abs[a]]]]>1 && UnsameQ[Head[status=fmap[{F[[Abs[a],1]],-F[[Abs[a],2]],F[[Abs[a],3]]}]],Missing] && M[[status]]==0 , *)
            If[F[[Abs[a],1]]==3 || F[[Abs[a],1]]==4,
                status=getF[{7-F[[Abs[a],1]],Sequence@@F[[Abs[a],2;;]]}];
                If[M[[status]]==0,cc=a;a=-1*Sign[a]*status;cc={a,-cc};addl[{a,cc}];]
                (* M[[Abs[a]]]=Sign[a];AppendTo[ML[[level]],{a,cc}];Morder[[Abs[a]]]=Length[ML[[level]]];
                Scan[If[#>0,++Cstatus[[#,2]];--Cstatus[[#,1]],++Clstatus[[-#,2]];--Clstatus[[-#,1]]]&,VC[[Sign[a],Abs[a]]]];
                Scan[If[#>0,--Cstatus[[#,1]],--Clstatus[[-#,1]]]&,VC[[-Sign[a],Abs[a]]]]; *)
            ]
        ]

    ]
];


End[];


EndPackage[];
