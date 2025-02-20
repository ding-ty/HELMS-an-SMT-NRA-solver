(* ::Package:: *)

BeginPackage["HELMS`"];


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


(*Score::usage="soring fucntion of celljump.";*)


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


LSPreproc::usage="ls preprocessing.";


InitVarInterval::usage="ls preprocessing.";


VarFixList::usage="ls preprocessing.";


UsingOutInvPropClause::usage="ls preprocessing.";


OutInvPropClause::usage="ls preprocessing.";


InvPropClause::usage="ls preprocessing.";


InvPropLinearAtom::usage="ls preprocessing.";


SolveOneVarLinear::usage="ls preprocessing.";


UpdateVarInterval::usage="ls preprocessing.";


UpValue::usage="ls preprocessing.";


OneVarLinearList::usage="ls preprocessing.";


TestLinear::usage="ls preprocessing.";


IniMethodZero::usage="initial value method 0.";


IniMethodOne::usage="initial value method 1.";


IniMethodTwo::usage="initial value method 2.";


LS::usage="one restart of local search.";


LSSolver::usage="local search solver.";


ELS::usage="one restart of extended local search.";


ELSSolver::usage="extended local search solver.";


ELS0::usage="one restart of extended local search for hybyrid solver phase 1.";


ELSSolver0::usage="extended local search solver for hybyrid solver phase 1.";


Preproc::usage="preprocessing input formula.";


Solver::usage="cooperation of mcsat and local search.";


NRASolver::usage="cooperation of mcsat and local search.";


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
];


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
];


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


SearchAndApplyOp1[polyList_, cnf_, varList_, varInterval_, (*varFixList_,*) x_, w_]:=
Module[{atomInFalseClause, xNew=x, falseAtomInTrueClause(*, var*), isCelljump=False},
	atomInFalseClause = GetAtomInFalseClause[polyList, cnf, varList, x];
    (*Print["atom in false clause: ",atomInFalseClause];*)
    Which[Length[atomInFalseClause] > 0, 
        {isCelljump, xNew} = MaxScoreOp1[polyList, cnf, varList, varInterval, (*varFixList,*) x, w, atomInFalseClause];
        (*{xNew, var} = MaxScoreOp1[polyList, cnf, varList, x, w, atomInFalseClause];*)
        (*Print["1: x (search atomInFalseClause): ", xNew,"\n"];*)
        If[isCelljump, (*\:5982\:679c\:66f4\:65b0\:4e86\:8d4b\:503c\:ff0c\:90a3\:4e48\:8fd4\:56de*)
            Return[{isCelljump, (*var,*) xNew}];
        ];
    ];

    falseAtomInTrueClause = GetFalseAtomInTrueClause[polyList, cnf, varList, x];
    (*Print["false atom in true clause", falseAtomInTrueClause];*)
    Which[Length[falseAtomInTrueClause] > 0, 
        {isCelljump, xNew} = MaxScoreOp1[polyList, cnf, varList, varInterval, (*varFixList,*) x, w, falseAtomInTrueClause];
        (*{xNew, var} = MaxScoreOp1[polyList, cnf, varList, x, w, falseAtomInTrueClause];*)
        (*Print["2: x (search falseAtomInTrueClause): ", xNew,"\n"];*)
    ];
    Return[{isCelljump, (*var,*) xNew}];
];


SearchAndApplyOp2[polyList_, cnf_, varList_, x_, w_]:=
Module[{atomInFalseClause, xNew, falseAtomInTrueClause, isCelljump},
	atomInFalseClause = GetAtomInFalseClause[polyList, cnf, varList, x]; 
    (*Print["atom in false clause: ",atomInFalseClause];*)
    Which[Length[atomInFalseClause] > 0, 
        (*Print[{polyList, cnf, varList, x, w, atomInFalseClause, invPolyList, invCnf}];
        Print[atomInFalseClause];*)
        {isCelljump, xNew} = MaxScoreOp2[polyList, cnf, varList, x, w, atomInFalseClause];
        (*Print["max score op 2-1: ",{isCelljump, xNew}];*)
        (*{xNew, var} = MaxScoreOp1[polyList, cnf, varList, x, w, atomInFalseClause];*)
        (*Print["1: x (search atomInFalseClause): ", xNew,"\n"];*)
        If[isCelljump, (*\:5982\:679c\:66f4\:65b0\:4e86\:8d4b\:503c\:ff0c\:90a3\:4e48\:8fd4\:56de*)
            Return[{isCelljump, (*var,*) xNew}];
        ];
    ];
    
    falseAtomInTrueClause = GetFalseAtomInTrueClause[polyList, cnf, varList, x];
    (*Print["false atom in true clause", falseAtomInTrueClause];*)
    Which[Length[falseAtomInTrueClause] > 0, 
        {isCelljump, xNew} = MaxScoreOp2[polyList, cnf, varList, x, w, falseAtomInTrueClause];
        (*Print["max score op 2-2: ",{isCelljump, xNew}];*)
        (*{xNew, var} = MaxScoreOp1[polyList, cnf, varList, x, w, falseAtomInTrueClause];*)
        (*Print["2: x (search falseAtomInTrueClause): ", xNew,"\n"];*)
    ];
    Return[{isCelljump, (*var,*) xNew}];
];


pp = 1;


(*Score[cnf_, polyValue_, w_]:=
Module[{atomScore, clauseScore, cnfScore},
	atomScore=Function[{atom},
		If[polyValue[[atom[[1]]]]*atom[[2]]>0,
			0,
			Abs[polyValue[[atom[[1]]]]]+pp
		]
	];
	clauseScore=Function[{clause},
		 Min[Table[atomScore[clause[[i]]],{i,Length[clause]}]]
	];
	Return[Total[Table[clauseScore[cnf[[i]]]*w[cnf[[i]]],{i,Length[cnf]}]]];
];*)


MaxScoreOp1[polyList_, cnf_, varList_, varInterval_, (*varFixList_,*) x_, w_, atomList_]:=
Module[{i, j, k, DistanceToTruth, DistanceToSatisfaction, Score, atomTruth, falseAtomList, isolation, tempx, distanceToX, xOld, xNew, maxScoreX, samplePoint, xVar(*, var=0*),tempAtomList, isCelljump=False}, 
	(*Print["max score op 1"];*)
	DistanceToTruth = Function[{atom0, x0}, 
	Which[Sign[(polyList[[atom0[[1]]]])/.x0] == Sign[atom0[[2]]], 0, 
	True, Abs[(polyList[[atom0[[1]]]])/.x0]+pp]];
	
	DistanceToSatisfaction = Function[{clause0, x0}, Min[Table[DistanceToTruth[clause0[[i]],x0],{i,Length[clause0]}]]];
	
	Score = Function[{cnf0, x0, x1}, 
	Sum[(DistanceToSatisfaction[cnf0[[i]], x0] - DistanceToSatisfaction[cnf0[[i]], x1])* w[cnf0[[i]]],{i,Length[cnf0]}]];
	
	(*Print[polyList];
	Print[cnf];
	Print[varList];
	Print[varInterval];
	Print[varFixList];
	Print[x];
	Print[w];
	Print[atomList];*)
	
	atomTruth = Function[atom0, Sign[(polyList/.x)[[atom0[[1]]]]] == Sign[atom0[[2]]]];
	falseAtomList = Select[atomList, atomTruth[#] == False &];
    tempAtomList = falseAtomList;
	(*Print["false atom list: ", falseAtomList];*)
	i = 0; maxScoreX = x; xOld = x;
	While[i <= Length[varList]-1,
		i++;
		(*If[MemberQ[varFixList,i],Continue[];];*)
		(*Print["\:5bf9",varList[[i]],"\:505a\:5b9e\:6839\:9694\:79bb"];*)
		tempx = x; 
		tempx[varList[[i]]] = varList[[i]]; 
		falseAtomList=Select[tempAtomList,!FreeQ[polyList[[#[[1]]]],varList[[i]]]&];
        (*Print[falseAtomList];
        Print[tempAtomList];*)
		(*Print["temp x: ", tempx];*)
        (*Print["Time: ",SessionTime[]];*)
        If[Length[falseAtomList]>0,
		    samplePoint = SamplePoint[polyList, falseAtomList, tempx]; (* \:5bf9\:7b2ci\:4e2a\:53d8\:91cf\:505a\:5b9e\:6839\:9694\:79bb\:ff0c\:5f97\:5230\:7684\:6837\:672c\:70b9*)
            (*Print["sample point: ",samplePoint];*)
        ,
            Continue[];
        ];
        (*Print["samplePoint: ",samplePoint];*)
		j = 1;
		While[j <= Length[falseAtomList],
			Switch[falseAtomList[[j,2]],
			-1, (* \:7ea6\:675f\:4e3ap(x)<0, op\:4e3a\:6cbfxi\:8f74\:65b9\:5411\:8ddd\:79bb\:539f\:6765\:8d4b\:503c\:6700\:8fd1\:7684\:8d1f\:6837\:672c\:70b9 *)
			xVar = Select[samplePoint[falseAtomList[[j]]], ((polyList[[falseAtomList[[j,1]]]]/.tempx)/.{varList[[i]]->#}) < 0 &]; (* \:8d1f\:6837\:672c\:70b9 *)
			xVar = Select[xVar, Min[varInterval[varList[[i]]]]<#<Max[varInterval[varList[[i]]]] &];
			(*Print[varList[[i]]," \:8d1f\:6837\:672c\:70b9: ",xVar]; *)
			Which[xVar != {},
			distanceToX = Table[Abs[xVar[[k]] - x[varList[[i]]]], {k, Length[xVar]}]; (* \:8d1f\:6837\:672c\:70b9\:5230\:539f\:6765\:8d4b\:503c\:7684\:8ddd\:79bb *)
			(*Print["distance to x: ",distanceToX];*)
			xNew =  x; 
			xNew[varList[[i]]] = xVar[[Position[distanceToX, Min[distanceToX]][[1,1]]]];
			(*Print["x new: ",xNew]; *)
			(*Print["Score: ",Score[cnf,xOld,xNew]]; *)
			(*Print["cnf: ",cnf];
			Print["x new: ",xNew];
			Print["w: ",w];*)
			Which[Score[cnf, xOld, xNew] > 0, maxScoreX = xNew; xOld = xNew; isCelljump=True;(*var = i;*)];
			(*Print["max score x: ", maxScoreX];*)
			],
			
			1, (* \:7ea6\:675f\:4e3ap(x)>0, op\:4e3a\:6cbfxi\:8f74\:65b9\:5411\:8ddd\:79bb\:539f\:6765\:8d4b\:503c\:6700\:8fd1\:7684\:6b63\:6837\:672c\:70b9 *)
			xVar = Select[samplePoint[falseAtomList[[j]]], ((polyList[[falseAtomList[[j,1]]]]/.tempx)/.{varList[[i]]->#}) > 0 &]; (* \:6b63\:6837\:672c\:70b9 *)
			xVar = Select[xVar, Min[varInterval[varList[[i]]]]<#<Max[varInterval[varList[[i]]]] &];
			(*Print[varList[[i]]," \:6b63\:6837\:672c\:70b9: ",xVar];*)
			Which[xVar != {},
			distanceToX = Table[Abs[xVar[[k]] - x[varList[[i]]]], {k, Length[xVar]}]; (* \:6b63\:6837\:672c\:70b9\:5230\:539f\:6765\:8d4b\:503c\:7684\:8ddd\:79bb *)
			xNew =  x; 
			xNew[varList[[i]]] = xVar[[Position[distanceToX, Min[distanceToX]][[1,1]]]];
			(*Print["cnf: ",cnf];
			Print["x new: ",xNew];
			Print["w: ",w];*)
			Which[Score[cnf, xOld, xNew] > 0, maxScoreX = xNew; xOld = xNew; isCelljump=True;(*var = i;*)];
			];
			];
			++j;
		];
	];
	(*Return[{maxScoreX,var}];*)
	Return[{isCelljump, maxScoreX}];
];


mcsat;


MaxScoreOp2[polyList_, cnf_, varList_, x_, w_, atomList_]:=
Module[{i, j, k, DistanceToTruth, DistanceToSatisfaction, Score, atomTruth, falseAtomList, falseAtomNum, 
		ansMCSAT={}, opList={}, tempx, xNew, clauseTruth, trueAtomInTrueClause, falseClause,
		calculatedAtom, uncalculatedAtom, atom, ans, xMCSAT, t, LenDenNum, tempPolyList, tempCnf}, 
	
	DistanceToTruth = Function[{atom0, x0}, 
	Which[Sign[(polyList[[atom0[[1]]]])/.x0] == Sign[atom0[[2]]], 0, 
	True, Abs[(polyList[[atom0[[1]]]])/.x0]+pp]];
	
	DistanceToSatisfaction = Function[{clause0, x0}, Min[Table[DistanceToTruth[clause0[[i]],x0],{i,Length[clause0]}]]];
	
	Score = Function[{cnf0, x0, x1}, 
	Sum[(DistanceToSatisfaction[cnf0[[i]], x0] - DistanceToSatisfaction[cnf0[[i]], x1])* w[cnf0[[i]]],{i,Length[cnf0]}]];
	
	atomTruth = Function[atom0, Sign[(polyList/.x)[[atom0[[1]]]]] == Sign[atom0[[2]]]];
	clauseTruth = Function[{clause0}, Or @@ Map[atomTruth[#]&, clause0]];
	falseAtomList = Select[atomList, atomTruth[#] == False &];
	falseAtomList=Table[falseAtomList[[i,1]]*falseAtomList[[i,2]],{i,Length[falseAtomList]}];
	falseAtomNum=Length[falseAtomList];
	(*Print["false atom list: ", falseAtomList];*)
	trueAtomInTrueClause=Select[Union[Select[cnf,clauseTruth[#]&]],atomTruth[#[[1]]]&];
	falseClause=Complement[cnf,trueAtomInTrueClause];
	falseClause=Table[Table[falseClause[[i,j,1]]*falseClause[[i,j,2]],{j,Length[falseClause[[i]]]}],{i,Length[falseClause]}];
	trueAtomInTrueClause=Table[trueAtomInTrueClause[[i,1,1]]*trueAtomInTrueClause[[i,1,2]],{i,Length[trueAtomInTrueClause]}];
	(*Print["false clause: ",falseClause];
	Print["true atom in true clause: ",trueAtomInTrueClause];*)
	mcsat=False;
	
	If[Length[varList]<=2,
		ansMCSAT=Select[MCSATSolver[{{#}},polyList,varList]&/@falseAtomList,#[[1]]!="unsat"&];
		(*Print[ansMCSAT];*)
		If[ansMCSAT!={},mcsat=True;Return[{True,ansMCSAT[[1,3]]}],Return[{False,x}]];
	];
	
	
	i=1;
	While[i<=Length[varList],
		j=i+1;
		While[j<=Length[varList],
			tempx=x;
			tempx[varList[[i]]] = varList[[i]];
			tempx[varList[[j]]] = varList[[j]];
			tempPolyList=polyList/.tempx;
			tempCnf=Union[falseClause,{#} & /@trueAtomInTrueClause];
			(*Print["temp cnf: ",tempCnf];
			Print["tempx: ",tempx];*)
			If[KeyExistsQ[calculatedMCSAT, {tempCnf,tempx,{varList[[i]],varList[[j]]}}],
				ans=calculatedMCSAT[{tempCnf,tempx,{varList[[i]],varList[[j]]}}];
				(*Print["ans calculated: ",ans];*)
				If[ans[[1]]!="unsat",mcsat=True;Return[{True,Association[x,ans[[-1]]]}]],
				(*Print["MCSAT input"];
				Print["cnf: ",tempCnf];
				Print["polyList: ",tempPolyList];
				Print["varList: ",{varList[[i]],varList[[j]]}];*)
				ans=MCSATSolver[tempCnf,tempPolyList,{varList[[i]],varList[[j]]}];
				(*Print["ans uncalculated: ",ans];*)
				If[ans[[1]]!="unsat",
					mcsat=True;
					Return[{True,Association[x,ans[[-1]]]}],
					calculatedMCSAT[{tempCnf,tempx,{varList[[i]],varList[[j]]}}]={False};
					(*Print["calculated MCSAT: ",calculatedMCSAT];*)
				];
			];
			++j;
		];
		++i;
	];
	
	i=1;
	While[i<=Length[varList],
		j=i+1;
		While[j<=Length[varList],
			tempx=x;
			tempx[varList[[i]]] = varList[[i]];
			tempx[varList[[j]]] = varList[[j]];
			tempPolyList=polyList/.tempx;
			calculatedAtom=Select[falseAtomList, KeyExistsQ[calculatedMCSAT, {Union[{#},trueAtomInTrueClause],tempx,{varList[[i]],varList[[j]]}}]&];
			uncalculatedAtom=Complement[falseAtomList,calculatedAtom];
			k=1;
			While[k<=Length[uncalculatedAtom],
				atom=uncalculatedAtom[[k]];
				(*Print["Join"];
				Print[atom];
				Print[trueAtomInTrueClause];
				Print[Union[{atom},trueAtomInTrueClause]];
				Print[invCnf];*)
				ans=MCSATSolver[{#}& /@ Union[{atom},trueAtomInTrueClause],tempPolyList,{varList[[i]],varList[[j]]}];
				(*Print["ans:",ans];*)
				(*Print["calculated MCSAT: ",calculatedMCSAT];*)
				If[ans[[1]]!="unsat",
					(*Print["ans[[-1]]: ",ans[[-1]]];*)
					xMCSAT=ans[[-1]];
					AppendTo[ansMCSAT,Association[x,xMCSAT]];
					calculatedMCSAT[{Union[{atom},trueAtomInTrueClause],tempx,{varList[[i]],varList[[j]]}}]={True,xMCSAT};
					(*Print["calculated MCSAT: ",calculatedMCSAT];*)
					,
					calculatedMCSAT[{Union[{atom},trueAtomInTrueClause],tempx,{varList[[i]],varList[[j]]}}]={False};
					(*Print["calculated MCSAT: ",calculatedMCSAT];*)
				];
				++k;
			];
			ansMCSAT=Union[ansMCSAT, calculatedMCSAT[Union[{#},trueAtomInTrueClause]][[-1]]&/@ Select[calculatedAtom,First[calculatedMCSAT[{Union[{#},trueAtomInTrueClause],newPolyList,{varList[[i]],varList[[j]]}}]]&]];
			(*Print["ansMCSAT: ",ansMCSAT];*)
			++j;
		];
		++i;
	];
	(*Print["opList\:ff1a ",opList];*)
	(*Print["ansMCSAT: ",ansMCSAT];*)
	xNew=MaximalBy[ansMCSAT,Score[cnf,x,#]&];
	If[Length[xNew]>0&&Score[cnf,x,xNew[[1]]]>0,
		Return[{True,RandomChoice[xNew]}],
		Return[{False,x}];
	];
];


calculatedMCSAT=<||>; (* {atomId,x,varList} -> {False},{True,xMCSAT} False=unsat, True=sat *) 


calculatedIsolation=<||>; (*polyY -> samplePoint*)


SamplePoint[polyList_, atomList_, assign_]:=
Module[{i, j, poly, polyY, isoInterval, samplePoint, midPoint, ans, rootNum, LenDenNum, Y},
	i = 1; ans= <||>;
	(*Print["atom list: ",atomList];*)
	While[i <= Length[atomList],
		(*Print["atom list: ", atomList];*)
		poly = (polyList[[atomList[[i,1]]]])/.assign;
		If[Length[Variables[Simplify[poly]]] == 0,
			(*Print["var: ", Variables[Simplify[poly]]];*)
			samplePoint = {},
			polyY = poly/.<|(Variables[poly][[1]])->Y|>;
			If[KeyExistsQ[calculatedIsolation, polyY], 
				samplePoint = calculatedIsolation[polyY], 
				rootNum = CountRoots[polyY,Y];
				(*Print[(*"poly: ",*) poly];
				Print["poly Y: ", polyY];*)
				If[rootNum==0, 
					samplePoint = {1},
					isoInterval = IsolatingInterval[#,10^-4]&/@(Root[polyY,#]&/@Range[rootNum]);
					(*isoInterval = RootIntervals[poly][[1]];*)
					samplePoint = Flatten[isoInterval];
					(*Print["samplePoint 0: ",samplePoint];*)
					If[Length[samplePoint]>0,
						midPoint = Table[(samplePoint[[2*i]] + samplePoint[[2*i+1]]) / 2, {i, Length[samplePoint]/2 - 1}];
						samplePoint = Union[{samplePoint[[1]]-1/10^4,samplePoint[[-1]]+1/10^4}, midPoint];
						(*samplePoint = Union[{samplePoint[[1]]-1/10,samplePoint[[-1]]+1/10},samplePoint, midPoint];*)
					];
					calculatedIsolation[polyY] = samplePoint;
				];
			];
		];
        AppendTo[ans, atomList[[i]] -> samplePoint];
		++i;
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


GradSearchAndApplyOp1[polyList_, cnf_, varList_, varInterval_, (*varFixList_,*) x_, w_]:=
Module[{ZeroVecTest, ScalVecTest, gradVecList, i, currVec, RandVec, randvec, randVecList, direction, atomInFalseClause, falseAtomInTrueClause, xNew=x, isCelljump=False},

	ZeroVecTest = Function[{vec}, And @@ Map[# == 0 &, vec]];
	ScalVecTest = Function[{vec, vecList}, i = SelectFirst[Range[Length[vec]], vec[[#]] != 0 &]; Or @@ Map[(#[[i]]/vec[[i]])*vec==#&, vecList]];
	gradVecList = Table[Map[D[polyList[[i]],#]&,varList]/.x, {i, Length[polyList]}]; (* \:68af\:5ea6\:5411\:91cf *)
	(*Print["grad vec: ", gradVecList]; *)
	currVec = Table[x[varList[[i]]],{i,Length[varList]}]; (* \:5f53\:524d\:70b9\:65b9\:5411 *)
	(*Print["current vec: ", currVec]; *)
	RandVec = Function[RandomInteger[{-1000, 1000}, Length[varList]]]; (* \:751f\:6210\:968f\:673a\:5411\:91cf *)
	(*RandVec = Function[randvec = RandomInteger[{-1000, 1000}, Length[varList]]; If[Count[randvec, 0] < Length[varList] - 1, randvec, RandVec[]]]; \:751f\:6210\:968f\:673a\:5411\:91cf *)
	randVecList = Table[RandVec[], {i,10}];
	(*Print["random vec: ", randVecList]; *)
	direction = Union[gradVecList, {currVec}, randVecList]; 
	(*Print["direction 1: ", direction];*) 
	direction = Delete[direction, Select[Range[Length[direction]], Table[ZeroVecTest[direction[[i]]],{i,Length[direction]}][[#]]&]];
	direction = Delete[direction, Select[Table[{i},{i,Length[direction]}], ScalVecTest[direction[[#1[[1]]]], direction[[1;;#1[[1]]-1]]]&]];(* \:65b9\:5411\:5411\:91cf\:7684\:5217\:8868 *)
	(*Print["direction 2: ", direction];*) 
	
	atomInFalseClause = GetAtomInFalseClause[polyList, cnf, varList, x]; 
	(*Print[atomInFalseClause];*)
	(*Print["GradMaxScoreOp: ",{polyList, cnf, varList, x, w, atomInFalseClause, direction}];*)
    If[Length[atomInFalseClause] > 0, 
        {isCelljump, xNew} = GradMaxScoreOp1[polyList, cnf, varList, varInterval, (*varFixList,*) x, w, atomInFalseClause, direction];
        If[isCelljump, Return[{isCelljump, xNew}]];
    ];
    falseAtomInTrueClause = GetFalseAtomInTrueClause[polyList, cnf, varList, x(*, direction*)];
    (*Print["GradMaxScoreOp: ",{polyList, cnf, varList, x, w, atomInFalseClause, direction}];*)
    If[Length[falseAtomInTrueClause]>0,
        {isCelljump, xNew} = GradMaxScoreOp1[polyList, cnf, varList, varInterval, (*varFixList,*) x, w, falseAtomInTrueClause, direction];
    ];
    Return[{isCelljump, xNew}];
];


GradSearchAndApplyOp2[polyList_, cnf_, varList_, x_, w_]:=
Module[{ZeroVecTest, ScalVecTest, gradVecList, i, currVec, RandVec, randvec, randVecList, direction, atomInFalseClause, falseAtomInTrueClause, xNew, isCelljump},
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
    If[Length[atomInFalseClause] > 0, 
        {isCelljump, xNew} = GradMaxScoreOp2[polyList, cnf, varList, x, w, atomInFalseClause, direction];
        If[isCelljump, Return[{isCelljump, xNew}];];
    ];
    falseAtomInTrueClause = GetFalseAtomInTrueClause[polyList, cnf, varList, x(*, direction*)];
    (*Print["GradMaxScoreOp: ",{polyList, cnf, varList, x, w, atomInFalseClause, direction}];*)
    {isCelljump, xNew} = GradMaxScoreOp2[polyList, cnf, varList, x, w, falseAtomInTrueClause, direction];
    Return[{isCelljump, xNew}];
];


GradMaxScoreOp1[polyList_, cnf_, varList_, varInterval_, (*varFixList_,*) x_, w_, atomList_, direction_]:=
Module[{i, j, k, DistanceToTruth, DistanceToSatisfaction, Score, atomTruth, falseAtomList, dir, polyListT, samplePoint, 
	tVar, distanceTo0, tNew, xOld, xNew, maxScoreX, t, var, xVar, varnum=Length[varList], n, isCelljump=False}, 
	DistanceToTruth = Function[{atom0, x0}, 
	Which[Sign[(polyList[[atom0[[1]]]])/.x0] == Sign[atom0[[2]]], 0, 
	True, Abs[(polyList[[atom0[[1]]]])/.x0]+pp]];
	
	DistanceToSatisfaction = Function[{clause0, x0}, Min[Table[DistanceToTruth[clause0[[i]],x0],{i,Length[clause0]}]]];
	
	Score = Function[{cnf0, x0, x1}, 
	Sum[(DistanceToSatisfaction[cnf0[[i]], x0] - DistanceToSatisfaction[cnf0[[i]], x1])* w[cnf0[[i]]],{i,Length[cnf0]}]];
	
	
	atomTruth = Function[atom0, Sign[(polyList/.x)[[atom0[[1]]]]] == Sign[atom0[[2]]]];
	falseAtomList = Select[atomList, atomTruth[#] == False &];
	(*Print["false atom: ", falseAtomList];*)
	var = varList[[1]];
	i = 1; maxScoreX = x; xOld = x;
	While[i <= Length[direction], 
		(*Print["5: ",SessionTime[]];*)
		dir = direction[[i]];
		(*Print["direction: ",dir];*)
		polyListT = polyList/.Table[varList[[k]] -> x[varList[[k]]] + dir[[k]] * t, {k, Length[varList]}]; (* \:6362\:5143, polyListT\:662f\:5173\:4e8et\:7684\:5355\:53d8\:5143\:591a\:9879\:5f0f\:7684\:5217\:8868 *)
		(*Print["poly list of t: ", polyListT];*)
		samplePoint = SamplePoint[polyListT, falseAtomList, <||>]; (* \:5bf9t\:505a\:5b9e\:6839\:9694\:79bb\:ff0c\:5f97\:5230\:7684\:6837\:672c\:70b9 *)
		(*Print["sample point: ",samplePoint];*)
		(*Print["6: ",SessionTime[]];*)
		j = 1;
		While[j <= Length[falseAtomList],
			Switch[falseAtomList[[j,2]],
				-1,(* \:7ea6\:675f\:4e3ap(x)<0, op\:4e3a\:6cbfdir\:65b9\:5411\:8ddd\:79bb\:539f\:6765\:8d4b\:503c\:6700\:8fd1(t\:8ddd\:79bb0\:6700\:8fd1)\:7684\:8d1f\:6837\:672c\:70b9 *)
				(*Print["switch -1"];*)
				tVar = Select[samplePoint[falseAtomList[[j]]], (polyListT[[falseAtomList[[j,1]]]]/.{t->#}) < 0 &]; (* \:8d1f\:6837\:672c\:70b9 *)
				(*Print["t var: ",tVar];*)
				xVar = Table[Association[Table[varList[[k]] -> x[varList[[k]]] + dir[[k]] * tVar[[n]], {k, Length[varList]}]],{n,Length[tVar]}];
				(*Print["x var: ", xVar];*)
				n=1;
				While[n<=varnum,
					xVar = Select[xVar, Min[varInterval[varList[[n]]]]<#[varList[[n]]]<Max[varInterval[varList[[n]]]] &];
					n++;
				];
				(*Print["\:8d1f\:6837\:672c\:70b9: ",xVar]; *)
				(*Print["t var: ",tVar];*)
				Which[xVar != {},
				distanceTo0 = Table[Abs[(xVar[[k]])[var]-x[var]], {k, Length[xVar]}]; (* \:8d1f\:6837\:672c\:70b9\:7b2c\:4e00\:4e2a\:53d8\:91cf\:7684\:53d8\:5316 *)
				(*tNew = tVar[[Position[distanceTo0, Min[distanceTo0]][[1]][[1]]]];*)
				xNew = xVar[[Position[distanceTo0, Min[distanceTo0]][[1,1]]]];
				(*Print["x new: ",xNew];Print["score: ",Score[cnf, xOld, xNew]];*)
				Which[Score[cnf, xOld, xNew] > 0, maxScoreX = xNew; xOld = xNew; isCelljump = True;];
				],
				
				1,(* \:7ea6\:675f\:4e3ap(x)>0, op\:4e3a\:6cbfdir\:65b9\:5411\:8ddd\:79bb\:539f\:6765\:8d4b\:503c\:6700\:8fd1(t\:8ddd\:79bb0\:6700\:8fd1)\:7684\:6b63\:6837\:672c\:70b9 *)
				tVar = Select[samplePoint[falseAtomList[[j]]], (polyListT[[falseAtomList[[j,1]]]]/.{t->#}) > 0 &]; (* \:6b63\:6837\:672c\:70b9 *)
				xVar = Table[Association[Table[varList[[k]] -> x[varList[[k]]] + dir[[k]] * tVar[[n]], {k, Length[varList]}]],{n,Length[tVar]}];
				n=1;
				While[n<=varnum,
					xVar = Select[xVar, Min[varInterval[varList[[n]]]]<#[varList[[n]]]<Max[varInterval[varList[[n]]]] &];
					n++;
				];
				(*Print["\:6b63\:6837\:672c\:70b9: ",xVar]; *)
				(*Print["t var: ",tVar];*)
				Which[xVar != {},
				distanceTo0 = Table[Abs[(xVar[[k]])[var]-x[var]], {k, Length[xVar]}]; (* \:6b63\:6837\:672c\:70b9\:5bf9\:5e94t\:52300\:7684\:8ddd\:79bb *)
				xNew = xVar[[Position[distanceTo0, Min[distanceTo0]][[1,1]]]];
				(*Print["x new: ",xNew];Print["score: ",Score[cnf, xOld, xNew]];*)
				Which[Score[cnf, xOld, xNew] > 0, maxScoreX = xNew; xOld = xNew; isCelljump = True;];
				];
				
			];
			j++;
		];
		i++;
	];
	Return[{isCelljump, maxScoreX}];
];


GradMaxScoreOp2[polyList_, cnf_, varList_, x_, w_, atomList_, direction_]:=
Module[{i, j, k, DistanceToTruth, DistanceToSatisfaction, Score, atomTruth, falseAtomList, falseAtomNum, 
		trueAtomInTrueClause, falseClause, clauseTruth, tempCnf, atom,
		ansMCSAT, ansMCSATX, opList={}, polyListT, t1, t2, xNew}, 
	DistanceToTruth = Function[{atom0, x0}, 
	Which[Sign[(polyList[[atom0[[1]]]])/.x0] == Sign[atom0[[2]]], 0, 
	True, Abs[(polyList[[atom0[[1]]]])/.x0]+pp]];
	
	DistanceToSatisfaction = Function[{clause0, x0}, Min[Table[DistanceToTruth[clause0[[i]],x0],{i,Length[clause0]}]]];
	
	Score = Function[{cnf0, x0, x1}, 
	Sum[(DistanceToSatisfaction[cnf0[[i]], x0] - DistanceToSatisfaction[cnf0[[i]], x1])* w[cnf0[[i]]],{i,Length[cnf0]}]];
	
	
	atomTruth = Function[atom0, Sign[(polyList/.x)[[atom0[[1]]]]] == Sign[atom0[[2]]]];
	clauseTruth = Function[{clause0}, Or @@ Map[atomTruth[#]&, clause0]];
	falseAtomList = Select[atomList, atomTruth[#] == False &];
	falseAtomList=Table[falseAtomList[[i,1]]*falseAtomList[[i,2]],{i,Length[falseAtomList]}];
	(*Print["false atom: ", falseAtomList];*)
	falseAtomNum=Length[falseAtomList];
	(*Print["false atom list: ", falseAtomList];*)
	trueAtomInTrueClause=Select[Union[Select[cnf,clauseTruth[#]&]],atomTruth[#[[1]]]&];
	falseClause=Complement[cnf,trueAtomInTrueClause];
	falseClause=Table[Table[falseClause[[i,j,1]]*falseClause[[i,j,2]],{j,Length[falseClause[[i]]]}],{i,Length[falseClause]}];
	trueAtomInTrueClause=Table[trueAtomInTrueClause[[i,1,1]]*trueAtomInTrueClause[[i,1,2]],{i,Length[trueAtomInTrueClause]}];
	(*Print["false clause: ",falseClause];*)
	(*Print["true atom in true clause: ",trueAtomInTrueClause];*)
	
	(*If[Length[varList]<=2,
		ansMCSAT=Select[MCSATSolver[{{#}},polyList,varList]&/@falseAtomList,#[[1]]!="unsat"&];
		(*Print[ansMCSAT];*)
		If[ansMCSAT!={},Return[ansMCSAT[[1,3]]],Return[x]];
	];*)
	
	tempCnf=Union[falseClause,{#} & /@trueAtomInTrueClause];
		
	i=1;
	While[i<=IntegerPart[Length[direction]/2],
		polyListT=polyList/.Table[varList[[k]] -> x[varList[[k]]] + direction[[2*i-1,k]]*t1 + direction[[2*i,k]]*t2, {k, Length[varList]}]; (* \:6362\:5143, polyListT\:662f\:5173\:4e8et1,t2\:7684\:591a\:9879\:5f0f\:7684\:5217\:8868 *)
		(*Print[polyListT];*)
		ansMCSAT=Select[MCSATSolver[tempCnf,polyListT,{t1,t2}]&/@falseAtomList,#[[1]]!="unsat"&];
		(*Print["ansMCSAT: ",ansMCSAT];*)
		ansMCSATX=Table[Association[Table[varList[[k]] -> x[varList[[k]]] + direction[[2*i-1,k]]*ansMCSAT[[j,3]][t1] + direction[[2*i,k]]*ansMCSAT[[j,3]][t2], {k, Length[varList]}]],{j,Length[ansMCSAT]}]; (*falseAtomList\:4e2d\:6bcf\:4e2a\:591a\:9879\:5f0f\:7ea6\:675f\:5173\:4e8ex[2i-1],x[2i]\:7684\:6837\:672c\:70b9*)
		(*Print["ansMCSATX: ",ansMCSATX];*)
		(*AppendTo[opList,MaximalBy[ansMCSATX,Score[cnf,x,#]&]];*)
		opList=Union[opList,ansMCSATX];
		(*Print["opList: ",opList];*)
		i++;
	];
	xNew=MaximalBy[opList,Score[cnf,x,#]&];
	If[Length[xNew]>0&&Score[cnf,x,xNew[[1]]]>0,Return[{True,RandomChoice[xNew]}],Return[{False,x}]];
	
	i=1;
	While[i<=IntegerPart[Length[direction]/2],
		polyListT=polyList/.Table[varList[[k]] -> x[varList[[k]]] + direction[[2*i-1,k]]*t1 + direction[[2*i,k]]*t2, {k, Length[varList]}]; (* \:6362\:5143, polyListT\:662f\:5173\:4e8et1,t2\:7684\:591a\:9879\:5f0f\:7684\:5217\:8868 *)
		(*Print[polyListT];*)
		k=1;
		While[k<=Length[falseAtomList],
			atom=falseAtomList[[k]];
			ansMCSAT=Select[MCSATSolver[{#}& /@ Union[{atom},trueAtomInTrueClause],polyListT,{t1,t2}]&/@falseAtomList,#[[1]]!="unsat"&];	
			(*Print["ansMCSAT: ",ansMCSAT];*)
			ansMCSATX=Table[Association[Table[varList[[k]] -> x[varList[[k]]] + direction[[2*i-1,k]]*ansMCSAT[[j,3]][t1] + direction[[2*i,k]]*ansMCSAT[[j,3]][t2], {k, Length[varList]}]],{j,Length[ansMCSAT]}]; (*falseAtomList\:4e2d\:6bcf\:4e2a\:591a\:9879\:5f0f\:7ea6\:675f\:5173\:4e8ex[2i-1],x[2i]\:7684\:6837\:672c\:70b9*)
			(*Print["ansMCSATX: ",ansMCSATX];*)
			(*AppendTo[opList,MaximalBy[ansMCSATX,Score[cnf,x,#]&]];*)
			opList=Union[opList,ansMCSATX];
			(*Print["opList: ",opList];*)
			k++;
		];
		i++;
	];
	xNew=MaximalBy[opList,Score[cnf,x,#]&];
	If[Length[xNew]>0&&Score[cnf,x,xNew[[1]]]>0,Return[{True,RandomChoice[xNew]}],Return[{False,x}]];
];


LSPreproc[polyList_, cnf_, varList_, linearList_, oneVarLinearList_]:=
Module[{init, varInterval, satAtomList, newCnf=cnf, ans, varFixList, newPolyList, newVarList,fixList},
	init = InitVarInterval[polyList, newCnf, varList, oneVarLinearList];
	If[Length[init]==0, Return[2]]; (* UNSAT *)
	{varInterval, satAtomList} = init;
	(*Print[polyList];
	Print[cnf];
	Print[varList];
	Print["var interval 1: ",varInterval];
	Print["sat atom list: ",satAtomList];
	Print["linear list: ", linearList];
	Print["one var linear list: ", oneVarLinearList];*)
	ans = UsingOutInvPropClause[polyList, newCnf, varList, varInterval, satAtomList, linearList, oneVarLinearList];
	(*Print["using out inv prop clause: ", ans];*)
	If[Length[ans]==0, Return[2];]; (* UNSAT *)
	If[ans[[1]]==False,
		newCnf = ans[[2]];
		varInterval = ans[[3]];
		varFixList = VarFixList[varList, varInterval];
		(*Print["var fix list: ",varFixList];*)
		If[Length[varFixList]==0 && varFixList==False, Return[1]]; (*"error VarFixList: \:6240\:6709\:53d8\:91cf\:5747\:53d6\:56fa\:5b9a\:503c, \:516c\:5f0f\:53ef\:6ee1\:8db3."*)
		(*Print[polyList];
		Print[Table[varList[[varFixList[[i]]]]->(Min[varInterval[varList[[varFixList[[i]]]]]]+Max[varInterval[varList[[varFixList[[i]]]]]])/2,{i,Length[varFixList]}]];
		Print[varInterval];*)
		fixList=Select[Range[Length[varList]], Max[varInterval[varList[[#]]]]-Min[varInterval[varList[[#]]]]>10^-5 &];
		(*Print[fixList];*)
		newPolyList = polyList/.Table[varList[[varFixList[[i]]]]->(Min[varInterval[varList[[varFixList[[i]]]]]]+Max[varInterval[varList[[varFixList[[i]]]]]])/2,{i,Length[varFixList]}];
		(*newVarList = Complement[varList, Table[varList[[varFixList[[i]]]],{i,Length[varFixList]}]];*)
		newVarList = Table[varList[[fixList[[i]]]],{i,Length[fixList]}];
		(*Print[newVarList];*)
		(*varInterval = Association[Table[newVarList[[i]]->varInterval[newVarList[[i]]],{i,Length[newVarList]}]];*)
		Return[{False, newPolyList, newCnf, newVarList, varInterval}];
		,
		Return[ans];
	];
];


InitVarInterval[polyList_, cnf_, varList_, oneVarLinearList_]:=
Module[{i, satAtomList={}, varInterval, atom, clause, polyIndex, relaSign, poly},
	varInterval = Association[Table[varList[[i]] -> Interval[{-Infinity, Infinity}], {i, Length[varList]}]];
	(*Print["var interval 2: ", varInterval];*)
	i=1;
	While[i<=Length[cnf],
		clause = cnf[[i]];
		If[Length[clause]==1,
			atom = clause[[1]];
			polyIndex = atom[[1]];
			If[MemberQ[oneVarLinearList, polyIndex],
				relaSign = atom[[2]];
				poly = polyList[[polyIndex]];
				(*Print["SolveOneVarLinear: ", {poly, relaSign, varInterval}];*)
				varInterval = SolveOneVarLinear[poly, relaSign, varInterval];
				If[Length[varInterval]==0, Return[False]]; (* UNSAT *)
				(*Print["var inv: ",varInterval];*)
				AppendTo[satAtomList, atom];
			];
		];
		i++;
	];
	(*Print["init var interval: ", {varInterval, satAtomList}];*)
	Return[{varInterval, satAtomList}];
];


VarFixList[varList_, varInterval_]:=
Module[{varFixList},
	varFixList = Select[Range[Length[varList]], Max[varInterval[varList[[#]]]]==Min[varInterval[varList[[#]]]] &];
	If[Length[varList]==Length[varFixList],
		(*Print["error VarFixList: \:6240\:6709\:53d8\:91cf\:5747\:53d6\:56fa\:5b9a\:503c, \:516c\:5f0f\:53ef\:6ee1\:8db3."];*)
		Return[False];
	];
	Return[varFixList];
];


UsingOutInvPropClause[polyList_, cnf_, varList_, varInterval_, satAtomList_, linearList_, oneVarLinearList_]:=
Module[{i, clause, varInterval0 = varInterval, satAtomList0 = satAtomList, unsatAtomList0 = {}, ansCnf = {}, temp},
	i=1;
	While[i<=Length[cnf],
		clause = cnf[[i]];
		temp = OutInvPropClause[clause, polyList, varList, varInterval0, satAtomList0, unsatAtomList0, linearList, oneVarLinearList];
		(*Print["OutInvPropClause: ", temp];*)
		If[Length[temp]==0, Return[False]]; (*UNSAT*)
		If[Length[temp[[1]]]==0 && temp[[1]]==False,
			(*Print["error: The CNF formula is unsatisfiable."];*)
			Return[False];
			,
			If[Length[temp[[1]]]==0 && temp[[1]]==True,
				varInterval0 = temp[[2]];
				satAtomList0 = temp[[3]];
				unsatAtomList0 = temp[[4]];
				,
				ansCnf = Join[ansCnf, {temp[[1]]}];
				varInterval0 = temp[[2]];
				satAtomList0 = temp[[3]];
				unsatAtomList0 = temp[[4]];
			];
		];
		i++;
	];
	(*Print["ans cnf: ", ansCnf];*)
	(*Print["unsat atom list: ", unsatAtomList0];*)
	If[Length[ansCnf]>0, 
		Return[{False, ansCnf, varInterval0}], 
		Return[{True, IniMethodZero[varList, varInterval0]}];
	];
];


OutInvPropClause[clause_, polyList_, varList_, varInterval_, satAtomList_, unsatAtomList_, linearList_, oneVarLinearList_]:=
Module[{i, unsatAtomNum=0, tempClause={}, atom, ans},
	i=1;
	While[i<=Length[clause],
		atom = clause[[i]];
		If[MemberQ[satAtomList, atom],
			Return[{True, varInterval, satAtomList, unsatAtomList}],
			If[MemberQ[unsatAtomList, atom],
				unsatAtomNum++,
				AppendTo[tempClause, atom];
			];
		];
		i++;
	];
	(*Print["temp clause: ", tempClause];*)
	(*Print["var inv: ", varInterval];*)
	(*Print["unsat atom num: ", unsatAtomNum];*)
	If[unsatAtomNum<Length[clause],
		ans = InvPropClause[tempClause, polyList, varList, varInterval, satAtomList, unsatAtomList, linearList, oneVarLinearList];
		If[Length[ans]==0, Return[False], Return[ans]]; (* UNSAT *)
		,
		Return[{False, varInterval, satAtomList, unsatAtomList}];
	];
];


InvPropClause[newClause_, polyList_, varList_, varInterval_, satAtomList_, unsatAtomList_, linearList_, oneVarLinearList_]:=
Module[{i, ansVarInterval=varInterval, ansSatAtomList=satAtomList, ansUnsatAtomList=unsatAtomList, ansClause={}, atom, polyIndex, poly, relaSign, temp, flag=0},
	i=1;
	While[i<=Length[newClause],
		atom = newClause[[i]];
		polyIndex = atom[[1]];
		poly = polyList[[polyIndex]];
		relaSign = atom[[2]];
		(*Print[poly];
		Print[relaSign];
		Print[varList];
		Print[ansVarInterval];*)
		If[MemberQ[linearList, polyIndex],
			temp = InvPropLinearAtom[poly, relaSign, varList, ansVarInterval];
			(*Print["inv prop linear atom: ", temp];*)
			If[temp==2,
				AppendTo[ansClause, atom],
				If[temp==1, 
					AppendTo[ansSatAtomList, atom];
					flag=1,
					If[Not[MemberQ[ansUnsatAtomList, atom]],
						AppendTo[ansUnsatAtomList, atom];
					];
				];
			],
			AppendTo[ansClause, atom];
		];
		i++;
	];
	
	If[Length[ansClause]==1,
		atom = ansClause[[1]];
		polyIndex = atom[[1]];
		If[MemberQ[oneVarLinearList, polyIndex],
			relaSign = atom[[2]];
			poly = polyList[[polyIndex]];
			(*Print["poly: ",poly];
			Print["rela sign: ", relaSign];
			Print["ans var interval: ", ansVarInterval];*)
			ansVarInterval = SolveOneVarLinear[poly, relaSign, ansVarInterval];
			If[Length[ansVarInterval]==0, Return[False]]; (* UNSAT *)
			AppendTo[ansSatAtomList, atom];
			flag=1;
		];
	];
	If[flag==1,
		Return[{True, ansVarInterval, ansSatAtomList, ansUnsatAtomList}],
		If[Length[ansClause]==0,
			Return[{False, ansVarInterval, ansSatAtomList, ansUnsatAtomList}],
			Return[{ansClause, ansVarInterval, ansSatAtomList, ansUnsatAtomList}];
		];
	];
];


InvPropLinearAtom[poly_, relaSign_, varList_, varInterval_]:=
Module[{i, coeffList, monoList, assignOne, ansInterval=Interval[{0,0}], coe, var, temp, ansLb, ansUb},
	(*sat 1, unsat 0, unknown 2*)
	monoList=MonomialList[poly,varList];
	assignOne=Association[Table[varList[[j]]->1,{j,Length[varList]}]];
	coeffList=Table[monoList[[j]]/.assignOne,{j,Length[monoList]}];
	monoList=Table[monoList[[j]]/coeffList[[j]],{j,Length[monoList]}];
	(*Print["coeff list: ", coeffList];
	Print["mono list: ", monoList];*)
	i=1;
	While[i<=Length[coeffList],
		coe = coeffList[[i]];
		var = monoList[[i]];
		If[IntegerQ[var] && var==1,
			temp = Interval[{coe,coe}],
			temp = coe*varInterval[var];
		];
		(*Print["temp: ", temp];*)
		ansInterval = temp+ansInterval;
		If[Min[ansInterval]==-Infinity && Max[ansInterval]==Infinity,
			Return[2];		
		];
		i++;
	];
	ansLb = Min[ansInterval];
	ansUb = Max[ansInterval];
	If[ansLb!=ansUb,
		If[relaSign==1,
			If[ansLb>=0, 
				Return[1],
				If[ansUb<=0,
					Return[0],
					Return[2];
				];
			],
			If[relaSign==-1,
				If[ansUb<=0,
					Return[1],
					If[ansLb>=0,
						Return[0],
						Return[2];
					];
				],
				If[ansLb<0 && ansUb>0, 
					Return[2],
					Return[0];
				];
			];
		],
		If[relaSign!=0,
			If[ansLb*relaSign>0, Return[1],Return[0];],
			If[ansLb==0, Return[1], Return[0];];
		];
	];
];


OneVarLinearList[polyList_]:=
Module[{i, linearList={}, oneVarLinearList={}, poly, isLinear, isLinearOneVar},
	i=1;
	While[i<=Length[polyList],
		poly = polyList[[i]];
		{isLinear, isLinearOneVar} = TestLinear[poly];
		If[isLinear,
			AppendTo[linearList, i];
			If[isLinearOneVar,
				AppendTo[oneVarLinearList, i];
			];
		];
		i++;
	];
	Return[{linearList, oneVarLinearList}];
];


TestLinear[poly_]:=
Module[{varSet, deg, y},
	varSet = Variables[poly];
	deg=Max[Exponent[(MonomialList[poly]/.Association[Map[#->y&,varSet]]),y]];
    If[deg==1,
        If[Length[varSet]==1,
            Return[{True, True}],
            Return[{True, False}];
        ],
        Return[{False, False}];
    ];
];


SolveOneVarLinear[poly_, relaSign_, varInterval_]:=
Module[{var, c1, c0, inqValue, ans},
	var = Variables[poly][[1]];
	c1 = Coefficient[poly, var, 1];
	c0 = Coefficient[poly, var, 0];
	inqValue = -c0/c1;
	(*Print["c1: ", c1," c0: ",c0];
	Print["inqValue: ",inqValue];*)
	If[relaSign*c1>0,
		ans = UpdateVarInterval[var,1,inqValue,varInterval];
		If[Length[ans]==0, Return[False], Return[ans]]; (* UNSAT *)
		,
		If[relaSign*c1<0,
			ans = UpdateVarInterval[var,-1,inqValue,varInterval];
			If[Length[ans]==0, Return[False], Return[ans]]; (* UNSAT *)
			,
			ans = UpdateVarInterval[var,0,inqValue,varInterval];
			If[Length[ans]==0, Return[False], Return[ans]]; (* UNSAT *)
		];
	];
];


UpdateVarInterval[var_, inqRela_, inqValue_, varInterval_]:=
Module[{varLb, varUb},
	varLb = Min[varInterval[var]];
	varUb = Max[varInterval[var]];
	If[varLb==varUb, 
		If[inqRela==1,
			If[varLb>inqValue, 
				Return[varInterval],
				(*Print["error: The CNF formula is unsat."];*)
				Return[False];
			],
			If[inqRela==-1,
				If[varLb<inqValue, 
					Return[varInterval],
					(*Print["error: Thr CNF formula is unsat."];*)
					Return[False];
				],
				If[varLb==inqValue,
					Return[varInterval],
					(*Print["error: Thr CNF formula is unsat."];*)
					Return[False];
				];
			];
		],
		If[inqRela==1,
			If[inqValue<=varLb,
				Return[varInterval],
				If[varLb<inqValue && inqValue<varUb,
					Return[UpValue[varInterval, var, Interval[{inqValue, varUb}]]],
					(*Print["error: The CNF formula is unsat."];*)
					Return[False];
				];
			],
			If[inqRela==-1,
				If[inqValue>=varUb,
					Return[varInterval],
					If[varLb<inqValue && inqValue<varUb,
						Return[UpValue[varInterval, var, Interval[{varLb, inqValue}]]]
					];
				],
				If[varLb<inqValue && inqValue<varUb,
					Return[UpValue[varInterval, var, Interval[{inqValue, inqValue}]]],
					(*Print["error: The CNF formula is unsat."];*)
					Return[False];
				];
			];
		];
	];
];


UpValue[x_, var_, varNewValue_]:=
Module[{tempx},
	tempx = x;
	tempx[var] = varNewValue;
	Return[tempx];
];


IniMethodZero[varList_, varInterval_]:=
Module[{i, x=<||>, var, lb, ub, nume, deno},
	(*Print["start ini method 0"];*)
	i=0;
	While[i<=Length[varList]-1,
		i++;
		var = varList[[i]];
		lb = Min[varInterval[var]];
		ub = Max[varInterval[var]];
		(*If[MemberQ[varFixList, i],
			x[var] = (lb+ub)/2;
			Continue[];
		];*)
		(*Print["lb: ", lb];
		Print["ub: ", ub];*)
		If[Not[IntersectingQ[{lb,ub},{-Infinity,Infinity}]],
			If[lb!=ub,
				If[lb<1 && 1<ub,
					x[var] = 1,
					deno = RandomInteger[{2,100}];
				    nume = RandomInteger[{1,deno}];
					x[var] = lb+(ub-lb)*nume/deno;
				],
				x[var] = lb;
			],
			If[lb==-Infinity && ub==Infinity,
				x[var]=1,
				If[Not[IntersectingQ[{lb},{-Infinity,Infinity}]],
					If[lb<1,
						x[var] = 1,
						x[var] = lb + 1/2;
					],
					If[1<ub,
						x[var] = 1,
						x[var] = ub - 1/2;
					];
				];
			];
		];
	];
	(*Print["end ini method 0"];*)
	Return[x];
];


IniMethodOne[varList_, varInterval_]:=
Module[{i, x=<||>, var, lb, ub, nume, deno},
	i=1;
	While[i<=Length[varList],
		var = varList[[i]];
		lb = Min[varInterval[var]];
		ub = Max[varInterval[var]];
		If[Not[IntersectingQ[{lb,ub},{-Infinity,Infinity}]],
			If[lb!=ub,
				If[lb<-1 && 1<ub,
					x[var]=RandomChoice[{1,-1}],
					deno = RandomInteger[{2,100}];
				    nume = RandomInteger[{1,deno}];
					x[var] = lb+(ub-lb)*nume/deno;
				],
				x[var]=lb;
			],
			If[lb==-Infinity && ub==Infinity,
				x[var] = RandomChoice[{1,-1}],
				If[Not[IntersectingQ[{lb},{-Infinity,Infinity}]],
					If[lb<-1,
						x[var] = RandomChoice[{1,-1}],
						x[var] = lb+1/2;
					],
					If[1<ub,
						x[var] = RandomChoice[{1,-1}],
						x[var] = ub-1/2;
					];
				];
			];
		];
		i++;
	];
	Return[x];
];


IniMethodTwo[varList_, varInterval_]:=
Module[{i, x=<||>, var, lb, ub, nume, deno},
	i=1;
	While[i<=Length[varList],
		var = varList[[i]];
		lb = Min[varInterval[var]];
		ub = Max[varInterval[var]];
		If[Not[IntersectingQ[{lb,ub},{-Infinity,Infinity}]],
			If[lb!=ub,
				deno = RandomInteger[{2,100}];
				nume = RandomInteger[{1,deno}];
			    x[var] = lb+(ub-lb)*nume/deno;
				,
				x[var]=lb;
			],
			If[lb==-Infinity && ub==Infinity,
				deno = RandomInteger[{2,100}];
				nume = RandomInteger[{1,deno}];
			    x[var] = -50+100*nume/deno;
			    ,
				If[Not[IntersectingQ[{lb},{-Infinity,Infinity}]],
					If[lb<50,
						deno = RandomInteger[{2,100}];
						nume = RandomInteger[{1,deno}];
			            x[var] = lb+(50-lb)*nume/deno;
						,
						x[var] = lb+1/2;
					],
					If[-50<ub,
						deno = RandomInteger[{2,100}];
						nume = RandomInteger[{1,deno}];
			            x[var] = -50+(ub+50)*nume/deno,
						x[var] = ub-1/2;
					];
				];
			];
		];
		i++;
	];
	Return[x];
];


(* ::Subsubsection:: *)
(*SMT*)
(*\:8f93\:5165\:ff1a\:4e25\:683c\:4e0d\:7b49\:5f0f\:7684\:65e0\:91cf\:8bcd\:5e03\:5c14\:7ec4\:5408*)
(*\:529f\:80fd\:ff1a\:6c42\:89e3SMT\:7684\:878d\:5408\:6c42\:89e3\:5668*)


SMT[formula_]:=
Module[{polyList,cnf,varList,clause},
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
	clause=Table[Table[cnf[[i,j,1]]*cnf[[i,j,2]],{j,Length[cnf[[i]]]}],{i,Length[cnf]}];
	Return[Solver[polyList,cnf,varList,clause]];
];


(* ::Subsubsection:: *)
(*Solver*)
(*\:529f\:80fd\:ff1a\:6c42\:89e3SMT\:7684\:878d\:5408\:6c42\:89e3\:5668*)


cntLS;


(*maxCntLS;*)


Preproc[polyList_, cnf0_, varList_]:=
Module[{F1=polyList,X=varList,cnf,F2,monoList,cons,consZero,highDegMono,highDegPoly,highDegVar,i,j,PRE=1},
	(*\:5904\:7406\:9ad8\:6b21\:5355\:53d8\:91cf\:5355\:9879\:5f0f*)
	monoList=MonomialList[F1];
	highDegMono=Select[Range[Length[monoList]],Length[monoList[[#]]]==1&&Max[Exponent[F1[[#]],X]]>1&];
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
			j++;
		];
		(*Print["cnf: ",F1];*)
		i++;
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
	Return[{F1,PRE}];
];


NRASolver[polyList_,cnf_,varList_,Clause1_, newPolyList_, newCnf_, newVarList_, varInterval_, time1_]:=
Module[{a,cc,i,j,xmap=<||>,fmap=<||>,F1=polyList,X=varList,F,Flevel,Fnow,conflictstatelist,Ci,Cli,Clause=Clause1,Clearn={},
        varnum,Clausenum,assignment,lorder,z,lnum,ML,M,Morder,VC,
        Cstatus,Clstatus,levell,levelc,levelcl,level,tmplevel,tmpc,tmpcl,status,nowc,conflict,
        getFnow,getFlevel,getClause,checkconflict,Polynomialroot,getorder,addl,getF, flag,
        samplecell,getsamplecell,nextsamplecell,maxlevel,deg,maxCntLS,cntAssign,completeAssignment,lsInit1={},ansLS,cntTLE,cad,cntCAD=0,maxCntCAD},   
        
       F=Map[{1,#}&,F1];
       assignment=Association[Map[#->0&,X]];
       (*Print[F];*)
       lnum=Length[F];
       (*Symmetry Check*)
       Module[{x0=X[[1]],C={}},
        Scan[
             If[(F1/.{#->x0,x0->#})==F1,AppendTo[F,{1,#-x0}];++lnum;AppendTo[C,{-lnum}];x0=#]&
         ,X[[2;;]]];
        (*Print[F];Print[Clause]*)
        If[Length[C]>Length[X]/2,(*Print["Find Symmetry: ",Map[Sequence@@F[[Abs[#],2]]&,C]];*)Clause={Sequence@@C,Sequence@@Clause}]
        ];
       (**)
       varnum=Length[X];
       Clausenum=Length[Clause];

       deg=Max[Exponent[(MonomialList[F1]/.Association[Map[#->y&,X]]),y]];
       (*Print["deg: ",deg];*)
       (*maxLS=0.5*Min[lnum,deg]*varnum;*)
       (*maxLS=2*(lnum+deg)*varnum;*)
       maxCntLS=0.1*Min[lnum,deg]*varnum;
       (*cntLS=0;*)
       cntTLE=0;
       
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
       Scan[AppendTo[levell[[lorder[[#]]]],#]&,Range[1,lnum]];
       Flevel=Table[0,lnum];
       Fnow=Table[0,lnum];VC={Table[{},lnum],Table[{},lnum]};
       Cstatus=Table[{0,0},Clausenum];Clstatus={};
       level=1; maxlevel=1;
       ML=Table[{},varnum];
       Morder=Table[0,lnum];M=Table[0,lnum];
       levelc=Table[{},varnum];levelcl=Table[{},varnum];
       conflictstatelist[[level]]={};
       (* Scan[If[Length[F[[#]]]>1,Flevel[[#]]=Polynomialroot[F[[#,1]]/.assignment,Abs[F[[#,2]]]],Flevel[[#]]=F[[#,1]]/.assignment]&,levell[[level]]];     *)
       Scan[(Flevel[[#]]=F[[#,2]]/.(X[[1]]->z))&,levell[[level]]];
       (* levelc[[level]]=Select[ Map[{Select[Clause[[#]],lorder[[Abs[#]]]==level& ],#}&,Ci[[level]]], Not[MemberQ[Map[Fnow[[#]]&,Select[Clause[[#[[2]]]],lorder[[Abs[#]]]<level&]],True]]& ]; *)
       levelc[[level]]=Map[{Clause[[#]],#}&,Ci[[level]]];
       Scan[(VC[[1]][[#]]={};VC[[-1]][[#]]={})&,levell[[level]] ];
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
       (*maxCntCAD=0.75*lnum;*)
       (*maxCntCAD=Infinity;*)
       While[True,
            (*++cntCAD;
            If[cntCAD>maxCntCAD,
                (*Print["CAD"];*)
		        cad=GenericCylindricalDecomposition[And@@Table[Or@@Table[If[Clause[[i,j]]<0,F1[[-Clause[[i,j]]]]<0,F1[[Clause[[i,j]]]]>0],{j,Length[Clause[[i]]]}],{i,Length[Clause]}],X];
                (*Print[cad];*)
                If[Length[cad[[1]]]==0 && Length[cad[[2]]]==0 && cad=={False,False},
                    Return[{"unsat","openCAD"}],
                    (*Return[{"CAD: sat",FindInstance[cad[[1]],varList]}];*)
                    Return[{"sat","openCAD"}];
                ];
            ];*)
            tmpc=MinimalBy[Select[Range[Length[levelc[[level]]]],Cstatus[[levelc[[level,#,2]],2]]==0&],Cstatus[[levelc[[level,#,2]],1]]&];
            tmpcl=MinimalBy[Select[Range[Length[levelcl[[level]]]],Clstatus[[levelcl[[level,#,2]],2]]==0&],Clstatus[[levelcl[[level,#,2]],1]]&];
            If[Length[tmpc]==0 && Length[tmpcl]==0,
                 assignment[X[[level]]]=FindMid[conflictstatelist[[level]]];
                 (* Scan[If[M[[#]]!=0,Fnow[[#]]=M[[#]]>0,If[Length[F[[#]]]>1,If[F[[#,2]]>0,Fnow[[#]]=assignment[X[[level]]]>Flevel[[#]],Fnow[[#]]=assignment[X[[level]]]<Flevel[[#]]],Fnow[[#]]=((F[[#,1]]/.assignment)>0)]]&,levell[[level]]]; *)
                 Scan[If[M[[#]]!=0,Fnow[[#]]=M[[#]]>0,If[F[[#,1]]!=5,Fnow[[#]]=getFnow[#]]]&,levell[[level]]];
                 Scan[If[M[[#]]==0 && F[[#,1]]==5,Fnow[[#]]=getFnow[#]]&,levell[[level]]];
                 
                 ++level;maxlevel=Max[level,maxlevel];
                 If[level>varnum,Return[{"sat","mcsat"}]];
                 conflictstatelist[[level]]={};
                 Scan[(M[[#]]=0)&,levell[[level]]];ML[[level]]={};
                 (* Scan[If[Length[F[[#]]]>1,Flevel[[#]]=Polynomialroot[F[[#,1]]/.assignment,Abs[F[[#,2]]]],Flevel[[#]]=F[[#,1]]/.assignment]&,levell[[level]]];     *)
                 Scan[(Flevel[[#]]=getFlevel[#])&,levell[[level]]];
                 (* levelc[[level]]=Select[ Map[{Select[Clause[[#]],lorder[[Abs[#]]]==level& ],#}&,Ci[[level]]], Not[MemberQ[Map[Fnow[[#]]&,Select[Clause[[#[[2]]]],lorder[[Abs[#]]]<level&]],True]]& ];
                 levelcl[[level]]=Select[ Map[{Select[Clearn[[#]],lorder[[Abs[#]]]==level& ],#}&,Cli[[level]]], Not[MemberQ[Map[Fnow[[#]]&,Select[Clearn[[#[[2]]]],lorder[[Abs[#]]]<level&]],True]]& ]; *)
                 levelc[[level]]=getClause[Clause,Ci[[level]]];
                 levelcl[[level]]=getClause[Clearn,Cli[[level]]];
                 Scan[(VC[[1]][[#]]={};VC[[-1]][[#]]={})&,levell[[level]] ];
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
                      While[status==0,
                           For[a = Select[conflict, lorder[[Abs[#]]]==level && M[[Abs[#]]]!=0 && Length[ML[[level,Morder[[Abs[#]]]]]] == 2 &],Length[a] != 0, 
                                       a = Select[conflict, lorder[[Abs[#]]]==level && M[[Abs[#]]]!=0 && Length[ML[[level,Morder[[Abs[#]]]]]] == 2 &],
                                conflict = Fold[ClauseResolve[#1, ML[[level,Morder[[Abs[#2]]],2]], #2] &, conflict, a];
                            ];
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
                                     tmplevel=Max[Map[lorder[[Abs[#]]]&,conflict]];
                                     ,
                                     AppendTo[Clearn,conflict];
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
            (*Print["cntAssign=",cntAssign,", Min=",Min[0.4*varnum,0.9*maxlevel]];*)
            (*Print["cntLS: ",cntLS,", maxCntLS: ",maxCntLS];*)
            cntAssign=level-1;
            If[Length[X]-2>cntAssign>Min[0.4*varnum,0.9*maxlevel](*&&cntLS<maxCntLS*)&&cntTLE<3,
                (*Print["mcsat-els"];*)
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
                        (*Print["mcsat-els var: ",{Take[X,-(varnum-cntAssign)],Intersection[newVarList,Take[X,-(varnum-cntAssign)]]}];*)
                        ansLS=TimeConstrained[
                            ELSSolver0[
                                F1/.Take[Normal[assignment],cntAssign],cnf,Take[X,-(varnum-cntAssign)],
                                newPolyList/.Take[Normal[assignment],cntAssign],newCnf,Intersection[newVarList,Take[X,-(varnum-cntAssign)]],
                                varInterval,1(*,maxCntLS,True*)
                            ],
                            1,{"unknown","ELS-TLE"}
                         ];
                        (*If[Length[ansLS]>=3,cntLS=ansLS[[3]]];*)
                        (*Print["assignment: ",assignment];*)
                        (*Print["completeAssignment: ",completeAssignment];*)
                        (*Print["ansLS: ",ansLS];*)
                        If[ansLS[[1]]=="sat",Return[{"sat","mcsat-ELS"}];(*cntLS=ansLS[[3]];*)];
                        If[ansLS[[2]]=="ELS-TLE",cntTLE++;];
                        (*Print["END: exLS"];*)
                    ],
                    (*\:591a\:4e2a\:672a\:8d4b\:503c\:53d8\:91cf: 3\:6b21\:4e0d\:6539\:53d8\:90e8\:5206\:8d4b\:503c\:7684LocalSearch *)
                    Scan[(completeAssignment[#]=1)&,X[[cntAssign+1;;]]];
                    (*Print["completeAssignment: ",completeAssignment];*)
                    If[Not[MemberQ[lsInit1,{assignment,completeAssignment}]],
                        AppendTo[lsInit1,{assignment,completeAssignment}];
                        (*Print["ExtendedLS: ",{ F1/.Take[Normal[assignment],cntAssign],cnf,Take[X,-(varnum-cntAssign)],
                                newPolyList/.Take[Normal[assignment],cntAssign],newCnf,Intersection[newVarList,Take[X,-(varnum-cntAssign)]],
                                varInterval,1}];*)
                        (*Print["mcsat-els var: ",{Take[X,-(varnum-cntAssign)],Intersection[newVarList,Take[X,-(varnum-cntAssign)]]}];*)
                        ansLS=TimeConstrained[
                            ELSSolver0[
                                F1/.Take[Normal[assignment],cntAssign],cnf,Take[X,-(varnum-cntAssign)],
                                newPolyList/.Take[Normal[assignment],cntAssign],newCnf,Intersection[newVarList,Take[X,-(varnum-cntAssign)]],
                                varInterval,3(*,maxCntLS,True*)
                            ],
                            1,{"unknown","ELS-TLE"}
                         ];
                        (*If[Length[ansLS]>=3,cntLS=ansLS[[3]]];*)
                        (*Print["ExtendedLS: ",{F1/.Take[Normal[assignment],cntAssign],cnf0,Take[X,-(varnum-cntAssign)],1,cntLS,maxCntLS}];*)
                        If[ansLS[[1]]=="sat",Return[{"sat","mcsat-ELS"}];(*cntLS=ansLS[[3]];*)];
                        If[ansLS[[2]]=="ELS-TLE",cntTLE++;];
                        (*Print["ansLS: ",ansLS];*)
                    ];
                ];
                (*Print[{cntLS,maxCntLS}];*)
                (*If[cntLS>maxCntLS,
                    (*Print["CAD"];*)
		            cad=GenericCylindricalDecomposition[And@@Table[Or@@Table[If[Clause[[i,j]]<0,F1[[-Clause[[i,j]]]]<0,F1[[Clause[[i,j]]]]>0],{j,Length[Clause[[i]]]}],{i,Length[Clause]}],X];
                    (*Print[cad];*)
                    If[Length[cad[[1]]]==0 && Length[cad[[2]]]==0 && cad=={False,False},
                        Return[{"unsat","openCAD"}],
                        (*Return[{"CAD: sat",FindInstance[cad[[1]],varList]}];*)
                        Return[{"sat","openCAD"}];
                    ];
                ];*)
            ];
            If[SessionTime[]-time1>20 && cntLS>maxCntLS,
                (*Print["Clause: ",Clause];
                Print["CAD start: ",And@@Table[Or@@Table[If[Clause1[[i,j]]<0,polyList[[-Clause1[[i,j]]]]<0,polyList[[Clause1[[i,j]]]]>0],{j,Length[Clause1[[i]]]}],{i,Length[Clause1]}]];
                Print["CAD var: ",varList];*)
                cad=GenericCylindricalDecomposition[And@@Table[And@@Table[Or@@Table[If[Clause1[[i,j]]<0,polyList[[-Clause1[[i,j]]]]<0,polyList[[Clause1[[i,j]]]]>0],{j,Length[Clause1[[i]]]}],{i,Length[Clause1]}],{i,Length[Clause]}],varList];
                (*Print[cad];*)
                If[Length[cad[[1]]]==0 && Length[cad[[2]]]==0 && cad=={False,False},
                    Return[{"unsat","openCAD"}],
                    (*Return[{"CAD: sat",FindInstance[cad[[1]],varList]}];*)
                    Return[{"sat","openCAD"}];
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
                            ]
                           ,
                           conflict=Nothing;
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


Solver[polyList_, cnf0_, varList_]:=
Module[{lnum=Length[polyList], ansLs, cad, deg, maxCntLS, y, fixList, notFixList, time1, clause=Table[Table[cnf0[[i,j,1]]*cnf0[[i,j,2]],{j,Length[cnf0[[i]]]}],{i,Length[cnf0]}],
        linearList, oneVarLinearList, preproc, newPolyList, newCnf, newVarList, varInterval, varFixList, polyList1, varList1},      

	{linearList, oneVarLinearList} = OneVarLinearList[polyList];
	preproc = LSPreproc[polyList, cnf0, varList, linearList, oneVarLinearList];
	(*Print["LS preprocessing: ", preproc];*)
	If[Length[preproc]==0,
		Switch[preproc,
			1, Return[{"sat", "LSPreprocessing"}], (*"error VarFixList: \:6240\:6709\:53d8\:91cf\:5747\:53d6\:56fa\:5b9a\:503c, \:516c\:5f0f\:53ef\:6ee1\:8db3."*)
			2, Return[{"unsat", "LSPreprocessing"}];(*"error: The CNF formula is unsatisfiable."*)
		];
	];
	If[preproc[[1]]==False,
		newPolyList =preproc[[2]];
		newCnf = preproc[[3]];
		newVarList = preproc[[4]];
		varInterval = preproc[[5]];
		,
		(*Return[{preproc[[1]],preproc[[2]],num,xnumTri,3}];*)
		Return[{"sat", "LSPreprocessing"}];
	];
	
	(*Print["varInterval: ",varInterval];*)
	
	(*invPolyList = {};
	invCnf={};
	inv=1;
	polyNum=Length[polyList];
	While[inv<=Length[varList],
		lb=Min[varInterval[varList[[inv]]]];
		ub=Max[varInterval[varList[[inv]]]];
		If[lb!=-Infinity && lb!=0,
			polyNum++;
			AppendTo[invPolyList,varList[[inv]]-lb];
			AppendTo[invCnf,{polyNum}];
		];
		If[ub!=Infinity && ub!=0,
			polyNum++;
			AppendTo[invPolyList,varList[[inv]]-ub];
			AppendTo[invCnf,{-polyNum}];
		];
		inv++;
	];*)
	
	If[Length[newVarList]<=2,
		ans=MCSATSolver[clause,polyList,varList];
		If[ans[[1]]=="sat",
			Return[{"sat","ELS"}],
			cntLS=0;
			(*cad=GenericCylindricalDecomposition[And@@Table[Or@@Table[If[cnf0[[i,j,2]]<0,polyList[[cnf0[[i,j,1]]]]<0,polyList[[cnf0[[i,j,1]]]]>0],{j,Length[cnf0[[i]]]}],{i,Length[cnf0]}],varList];
            If[Length[cad[[1]]]==0 && Length[cad[[2]]]==0 && cad=={False,False},
                Return[{"unsat","openCAD"}],
                (*Return[{"CAD: sat",FindInstance[cad[[1]],varList]}];*)
                Return[{"sat","openCAD"}];
            ];*)
			Return[
				NRASolver[polyList,cnf0,varList,clause,newPolyList,newCnf,newVarList,varInterval,SessionTime[]]
			];
		];
	];
	
	notFixList = Select[Range[Length[varList]], Max[varInterval[varList[[#]]]]-Min[varInterval[varList[[#]]]]>10^-5 &];
	fixList = Complement[Range[Length[varList]],notFixList];
	polyList1 = polyList/.Table[varList[[fixList[[i]]]]->(Min[varInterval[varList[[fixList[[i]]]]]]+Max[varInterval[varList[[fixList[[i]]]]]])/2,{i,Length[fixList]}];
	varList1 = Table[varList[[notFixList[[i]]]],{i,Length[notFixList]}];
	newPolyList = newPolyList/.Table[varList[[fixList[[i]]]]->(Min[varInterval[varList[[fixList[[i]]]]]]+Max[varInterval[varList[[fixList[[i]]]]]])/2,{i,Length[fixList]}];
	cntLS=0;
	(*deg=Max[Exponent[(MonomialList[polyList1]/.Association[Map[#->y&,varList1]]),y]];
	maxCntLS=0.1*Min[lnum,deg]*Length[varList1];*)
	(*LS + ExtendedLocalSearch + open cad*)
	(*Print["ELS start: ",SessionTime[]];*)
	(*ansLs=TimeConstrained[ELSSolver0[polyList,cnf0,varList,newPolyList,newCnf,newVarList,clause,varInterval,invPolyList,invCnf,1,10,False],1,{"unknown","ELS-TLE"}];*)
	(*ansLs=TimeConstrained[ELSSolver0[polyList1,cnf0,varList1,newPolyList,newCnf,newVarList,varInterval,1,10,False],1,{"unknown","ELS-TLE"}];*)
	ansLs=TimeConstrained[ELSSolver0[polyList1,cnf0,varList1,newPolyList,newCnf,newVarList,varInterval,1(*,maxCntLS,False*)],1,{"unknown","ELS-TLE"}];
	(*Print["ELS end: ",SessionTime[]];*)
	(*Print["cntLS= ",cntLS," maxCntLS= ",maxCntLS];*)
	If[ansLs[[1]]!="unknown",Return[ansLs];(*cntLS=ansLs[[3]];*)(*cntLS=0;*)];
	(*Print["ELS: ",ansLs];*)
	(*Print[{cntLS,maxCntLS}];*)
	(*If[cntLS>maxCntLS||ansLs[[2]]=="openCAD",
		Print["cad start"];
		cad=TimeConstrained[
			GenericCylindricalDecomposition[And@@Table[Or@@Table[If[cnf0[[i,j,2]]<0,polyList[[cnf0[[i,j,1]]]]<0,polyList[[cnf0[[i,j,1]]]]>0],{j,Length[cnf0[[i]]]}],{i,Length[cnf0]}],varList]
			,2,{"unknown","CAD-TLE"}];
        If[Length[cad[[1]]]==0 && Length[cad[[2]]]==0 && cad=={False,False},
            Return[{"unsat","openCAD"}],
            (*Return[{"CAD: sat",FindInstance[cad[[1]],varList]}];*)
            Return[{"sat","openCAD"}];
        ];
    ];*)
    time1=SessionTime[];
	(*Print["mcsat start: ",{polyList,cnf0,varList,clause,newPolyList,newCnf,newVarList,varInterval,time1}];*)
	Return[
		NRASolver[polyList,cnf0,varList,clause,newPolyList,newCnf,newVarList,varInterval,time1]
	];
];


(* ::Subsubsection:: *)
(*ELSSolver*)
(*\:529f\:80fd\:ff1a\:6c42\:89e3SMT\:7684\:6269\:5c55\:5c40\:90e8\:641c\:7d22\:6c42\:89e3\:5668\:ff0c\:524d\:4e24\:7ea7\:7b56\:7565\:662fLS\:7684celljump\:ff0c\:540e\:4e24\:7ea7\:7b56\:7565\:662fExtendedLS\:7684celljump*)


ELSSolver[polyList_, cnf_, varList_, lsLimit_,maxCntLS_]:=
Module[{cnt=1,init,lsInit={},ans,cons,consZero,LenDenNum,lnum,varnum,deg,clauses,
		linearList,oneVarLinearList,preproc,newPolyList,newCnf,newVarList,varInterval,varFixList, varList1, polyList1,
		invPolyList,invCnf,inv,polyNum,lb,ub,fixList, notFixList},
	
	cntLS=0;
	{linearList, oneVarLinearList} = OneVarLinearList[polyList];
	preproc = LSPreproc[polyList, cnf, varList, linearList, oneVarLinearList];
	(*Print["LS preprocessing: ", preproc];*)
	If[Length[preproc]==0,
		Switch[preproc,
			1, Return[{"sat", "LSPreprocessing"}], (*"error VarFixList: \:6240\:6709\:53d8\:91cf\:5747\:53d6\:56fa\:5b9a\:503c, \:516c\:5f0f\:53ef\:6ee1\:8db3."*)
			2, Return[{"unsat", "LSPreprocessing"}];(*"error: The CNF formula is unsatisfiable."*)
		];
	];
	If[preproc[[1]]==False,
		newPolyList =preproc[[2]];
		newCnf = preproc[[3]];
		newVarList = preproc[[4]];
		varInterval = preproc[[5]];
		,
		(*Return[{preproc[[1]],preproc[[2]],num,xnumTri,3}];*)
		Return[{"sat", "LSPreprocessing"}];
	];
	(*Print["varInterval: ",varInterval];*)
	notFixList = Select[Range[Length[varList]], Max[varInterval[varList[[#]]]]-Min[varInterval[varList[[#]]]]>10^-5 &];
	fixList = Complement[Range[Length[varList]],notFixList];
	polyList1 = polyList/.Table[varList[[fixList[[i]]]]->(Min[varInterval[varList[[fixList[[i]]]]]]+Max[varInterval[varList[[fixList[[i]]]]]])/2,{i,Length[fixList]}];
	varList1 = Table[varList[[notFixList[[i]]]],{i,Length[notFixList]}];
	newPolyList = newPolyList/.Table[varList[[fixList[[i]]]]->(Min[varInterval[varList[[fixList[[i]]]]]]+Max[varInterval[varList[[fixList[[i]]]]]])/2,{i,Length[fixList]}];
	
	(*invPolyList = {};
	invCnf={};
	inv=1;
	polyNum=Length[polyList];
	While[inv<=Length[varList],
		lb=Min[varInterval[varList[[inv]]]];
		ub=Max[varInterval[varList[[inv]]]];
		If[lb!=-Infinity,
			polyNum++;
			AppendTo[invPolyList,varList[[inv]]-lb];
			AppendTo[invCnf,{polyNum}];
		];
		If[ub!=Infinity,
			polyNum++;
			AppendTo[invPolyList,varList[[inv]]-ub];
			AppendTo[invCnf,{-polyNum}];
		];
		inv++;
	];*)
	
	If[Length[newVarList]<=2,
		clauses=Table[Table[cnf[[i,j,1]]*cnf[[i,j,2]],{j,Length[cnf[[i]]]}],{i,Length[cnf]}];
		ans=MCSATSolver[clauses,polyList,varList];
		Return[{ans[[1]],ans[[2]]}];
	];
	
	While[cnt<=lsLimit,
		Which[cnt==1,
			(*Print["ELS start: ",cnt];*)
			(*Print["varList, varInterval: ",{varList, varInterval}];*)
			init=IniMethodZero[newVarList, varInterval];
			(*Print["init: ",init];*)
			AppendTo[lsInit,init];
			(*Print["ELS input: ",{init,polyList1,cnf,varList1,newPolyList,newCnf,newVarList,varInterval,maxCntLS}];*)
			ans=ELS[init,polyList1,cnf,varList1,newPolyList,newCnf,newVarList,varInterval,maxCntLS];
            If[ans[[1]]!="unknown",Return[ans];];
			cnt++,
			cnt>=2&&cnt<=6,
			(*Print["ELS start: ",cnt];*)
			(*init=Association[Map[#->RandomChoice[{-1,1}]&,varList]];*)
			init=IniMethodOne[varList, varInterval];
			(*Print["init: ",init];*)
			If[Not[MemberQ[lsInit,init]],
                AppendTo[lsInit,init];
                ans=ELS[init,polyList1,cnf,varList1,newPolyList,newCnf,newVarList,varInterval,maxCntLS];
                If[ans[[1]]!="unknown",Return[ans];];
            ];
            cnt++,
            cnt>=7,
            (*Print["ELS start: ",cnt];*)
            init=IniMethodTwo[varList, varInterval];
			(*init=Association[Map[#->RandomInteger[{-50*(cnt-6),50*(cnt-6)}]&,varList]];*)
            (*Print["init: ",init];*)
            If[Not[MemberQ[lsInit,init]],
                AppendTo[lsInit,init];
                ans=ELS[init,polyList1,cnf,varList1,newPolyList,newCnf,newVarList,varInterval,maxCntLS];
                If[ans[[1]]!="unknown",Return[ans];];
            ];
            cnt++;
		];
	];
	Return[{"unknown","ELS"}];
];


ELS[x0_, polyList_, cnf_, varList_, newPolyList_, newCnf_, newVarList_, varInterval_, maxCntLS_]:=
Module[{i, x, w, isAxis, x1, x2, isDir, var, ans,
		cnt=1,init,lsInit={},(*maxCntLS,*)varListLast,vars=Length[varList],varList2,
		clauses,y,cons,consZero,cycle={},cad,mcsatPoly,LenDenNum,varnum=Length[varList]},
	
	clauses=Table[Table[cnf[[i,j,1]]*cnf[[i,j,2]],{j,Length[cnf[[i]]]}],{i,Length[cnf]}];
	
	varList2=Take[varList,vars-2];
	varListLast=Take[varList,-2];
	(*maxCntLS=2*Min[Length[polyList],Max[Exponent[(MonomialList[polyList]/.Association[Map[#->y&,varList]]),y]]]*vars;*)
	(*Print["maxCntLS: ",maxCntLS];*)
	x = x0;
	w = Association[Table[cnf[[i]] -> 1, {i, Length[cnf]}]];
	(*Print["initial x: ", x];*)
	
	While[True,
		(*Print["x: ",x];*)
		(*sat check*)
		If[SatCheck[polyList, cnf, varList, x],Return[{"sat","ELS"}]];
		(*Print["poly sign: ",Table[Sign[polyList/.x][[i]]*i,{i,Length[polyList]}]];*)
		x1=x;
		x1[varListLast[[1]]]=varListLast[[1]];
		x1[varListLast[[2]]]=varListLast[[2]];
		mcsatPoly=polyList/.x1;
		If[MCSATSolver[clauses,mcsatPoly,varListLast][[1]]=="sat",Return[{"sat","ELS"}]];
		
		(*cad*)
		If[cntLS>maxCntLS,
		    cad=GenericCylindricalDecomposition[And@@Table[Or@@Table[If[cnf[[i,j,2]]<0,polyList[[cnf[[i,j,1]]]]<0,polyList[[cnf[[i,j,1]]]]>0],{j,Length[cnf[[i]]]}],{i,Length[cnf]}],varList];
            If[Length[cad[[1]]]==0 && Length[cad[[2]]]==0 && cad=={False,False},
                Return[{"unsat","openCAD"}],
                (*Return[{"CAD: sat",FindInstance[cad[[1]],varList]}];*)
                Return[{"sat","openCAD"}];
            ];
        ];
        
        (*simplify*)
        (*Print["before x: ",x];*)
        i=1;
		While[i<=varnum,
			If[Max[IntegerLength[Denominator[x[[i]]]],IntegerLength[Abs[Numerator[x[[i]]]]]]>15,
				LenDenNum=Min[IntegerLength[Denominator[x[[i]]]],IntegerLength[Abs[Numerator[x[[i]]]]]];
				x[[i]]=IntegerPart[Numerator[x[[i]]]/10^(LenDenNum-2)]/IntegerPart[Denominator[x[[i]]]/10^(LenDenNum-2)];
			];
			If[IntegerLength[Denominator[x[[i]]]]-IntegerLength[Numerator[x[[i]]]]>5,x[[i]]=0;];
			++i;
		];
		(*Print["simplify x: ", x];*)
		
		
		(*celljump*)
		{isAxis(*, var*), x1} = SearchAndApplyOp1[newPolyList,newCnf,newVarList, varInterval, x, w];  (* \:6cbf\:5750\:6807\:8f74celljump 1 *)
		(*Print["celljump axis 1: ",isAxis,x1];*)
		cntLS++;
		If[isAxis&&Not[MemberQ[cycle,x1]],
			AppendTo[cycle,x1]; x = x1,
			w = UpdateWeight[polyList, cnf, varList, x, w];
			{isDir, x1} = GradSearchAndApplyOp1[newPolyList,newCnf,newVarList, varInterval, x, w];  (* \:6cbf\:67d0\:4e9b\:65b9\:5411celljump 1 *)
			(*Print["celljump direction 1: ",isDir,x1];*)
			cntLS++;
			If[isDir&&Not[MemberQ[cycle,x1]],
				AppendTo[cycle,x1]; x = x1,
				w = UpdateWeight[polyList, cnf, varList, x, w];
				{isAxis, x1} = SearchAndApplyOp2[polyList, cnf, varList, x, w]; (* \:6cbf\:5750\:6807\:8f74celljump 2 *)
				Print["celljump axis 2: ",isAxis,x1];
				If[mcsat,Return[{"sat","ELS"}]];
				cntLS++;
				If[isAxis&&Not[MemberQ[cycle,x1]], 
				    AppendTo[cycle,x1]; x = x1, 
				    w = UpdateWeight[polyList, cnf, varList, x, w];
				    (*Print["w: ",w];*)
                    {isDir, x1} = GradSearchAndApplyOp2[polyList, cnf, varList, x, w]; (* \:6cbf\:67d0\:4e9b\:65b9\:5411celljump 2 *)
					(*Print["celljump direction 2: ",isDir,x1];*)
					x2=x;
				    If[Length[varList2]>=2,
						x2[varList2[[1]]]=x1[varList2[[1]]];
						x2[varList2[[2]]]=x1[varList2[[2]]],
						x2[varList2[[1]]]=x1[varList2[[1]]];
					];
					(*Print["celljump direction 2: ",isDir,x2];*)
				    If[MemberQ[cycle,x2],Return[{"unknown","ELS"}];];
				    If[isDir,
				        AppendTo[cycle,x2]; x = x2,
				        (*w = UpdateWeight[polyList, cnf, varList, x, w];*)
				        Return[{"unknown","ELS"}];
					];
				];
			];
		];
		
	];
	Return[{"unknown","ELS"}];
];


ELSSolver0[polyList_, cnf_, varList_, newPolyList_, newCnf_, newVarList_, varInterval_, lsLimit_(*,maxCntLS_,bool_*)]:=
Module[{cnt=1,init,lsInit={},ans,cons,consZero,LenDenNum,lnum,varnum,deg,clauses},

	While[cnt<=lsLimit,
		Which[cnt==1,
			(*Print["ELS start: ",cnt];*)
			init=IniMethodZero[varList, varInterval];
			AppendTo[lsInit,init];
			ans=ELS0[init,polyList,cnf,varList,newPolyList,newCnf,newVarList,varInterval(*,maxCntLS,bool*)];
			(*Print["ELS0: ",ans];*)
            If[ans[[1]]!="unknown",(*Return[Join[ans,{cnt,Length[polyList0],Length[cnf0],Length[varList]}]]*)Return[ans];];
			cnt++,
			cnt>=2&&cnt<=6,
			(*Print["ELS start: ",cnt];*)
			(*init=Association[Map[#->RandomChoice[{-1,1}]&,varList]];*)
			init=IniMethodOne[varList, varInterval];
			(*Print["init: ",init];*)
			If[Not[MemberQ[lsInit,init]],
                AppendTo[lsInit,init];
                ans=ELS0[init,polyList,cnf,varList,newPolyList,newCnf,newVarList,varInterval(*,maxCntLS,bool*)];
                If[ans[[1]]!="unknown",(*Return[Join[ans,{cnt,Length[polyList0],Length[cnf0],Length[varList]}]]*)Return[ans];];
            ];
            cnt++,
            cnt>=7,
            (*Print["ELS start: ",cnt];*)
            init=IniMethodTwo[varList, varInterval];
			(*init=Association[Map[#->RandomInteger[{-50*(cnt-6),50*(cnt-6)}]&,varList]];*)
            (*Print["init: ",init];*)
            If[Not[MemberQ[lsInit,init]],
                AppendTo[lsInit,init];
                ans=ELS0[init,polyList,cnf,varList,newPolyList,newCnf,newVarList,varInterval(*,maxCntLS,bool*)];
                If[ans[[1]]!="unknown",(*Return[Join[ans,{cnt,Length[polyList0],Length[cnf0],Length[varList]}]]*)Return[ans];];
            ];
            cnt++;
		];
	];
	If[ans[[2]]=="openCAD",Return[{"unknown","openCAD"}],Return[{"unknown","ELS"}];];
];


ELS0[x0_, polyList_, cnf_, varList_, newPolyList_, newCnf_, newVarList_, varInterval_(*, maxCntLS_, bool_*)]:=
Module[{i, x, w, isAxis, x1, x2, isDir, var, clauses,
		cnt=1,init,lsInit={},vars=Length[varList],varList2,varListLast,
		y,cons,consZero,cycle={},cad,mcsatPoly,LenDenNum},
	(*Print[polyList];Print[cnf];Print[newVarList];
	Print[newPolyList];Print[newCnf];Print[varList];*)
	clauses=Table[Table[cnf[[i,j,1]]*cnf[[i,j,2]],{j,Length[cnf[[i]]]}],{i,Length[cnf]}];
	(*If[vars<=2,Return[MCSATSolver[clauses,polyList,varList]]];*)
	varList2=Take[varList,vars-2];
	varListLast=Take[varList,-2];
	
	(*maxCntLS=2*Min[Length[polyList],Max[Exponent[(MonomialList[polyList]/.Association[Map[#->y&,varList]]),y]]]*vars;*)
	(*Print["maxCntLS: ",maxCntLS];*)
	x = x0;
	w = Association[Table[cnf[[i]] -> 1, {i, Length[cnf]}]];
	(*Print["initial x: ", x];*)
	
	While[True,
		(*Print[SessionTime[]];*)
		(*sat check*)
		If[SatCheck[polyList, cnf, varList, x],Return[{"sat","ELS"(*,cntLS*)}]];
		(*Print["poly sign: ",Table[Sign[polyList/.x][[i]]*i,{i,Length[polyList]}]];*)
		x1=x;
		x1[varListLast[[1]]]=varListLast[[1]];
		x1[varListLast[[2]]]=varListLast[[2]];
		mcsatPoly=polyList/.x1;
		(*Print[{clauses,mcsatPoly,varListLast}];
		Print[MCSATSolver[clauses,mcsatPoly,varListLast]];*)
		If[MCSATSolver[clauses,mcsatPoly,varListLast][[1]]=="sat",Return[{"sat","ELS"}]];
		
		(*cad*)
		(*Print["cntLS: ",cntLS, ", maxCntLS: ", maxCntLS];*)
		(*If[bool && cntLS>maxCntLS,
			(*Print["CAD"];*)
		    cad=GenericCylindricalDecomposition[And@@Table[Or@@Table[If[cnf[[i,j,2]]<0,polyList[[cnf[[i,j,1]]]]<0,polyList[[cnf[[i,j,1]]]]>0],{j,Length[cnf[[i]]]}],{i,Length[cnf]}],varList];
            If[Length[cad[[1]]]==0 && Length[cad[[2]]]==0 && cad[[1]]==False && cad[[2]]==False,
                Return[{"unknown","openCAD"}],
                (*Return[{"CAD: sat",FindInstance[cad[[1]],varList]}];*)
                Return[{"sat","openCAD"}];
            ];
        ];*)
        
        (*simplify*)
        (*Print["before x: ",x];*)
        i=1;
		While[i<=vars,
			If[Max[IntegerLength[Denominator[x[[i]]]],IntegerLength[Abs[Numerator[x[[i]]]]]]>15,
				LenDenNum=Min[IntegerLength[Denominator[x[[i]]]],IntegerLength[Abs[Numerator[x[[i]]]]]];
				x[[i]]=IntegerPart[Numerator[x[[i]]]/10^(LenDenNum-2)]/IntegerPart[Denominator[x[[i]]]/10^(LenDenNum-2)];
			];
			If[IntegerLength[Denominator[x[[i]]]]-IntegerLength[Numerator[x[[i]]]]>5,x[[i]]=0;];
			++i;
		];
		(*Print["simplify x: ", x];*)
		
		
		(*celljump*)
		{isAxis(*, var*), x1} = SearchAndApplyOp1[newPolyList,newCnf,newVarList, varInterval, x, w];  (* \:6cbf\:5750\:6807\:8f74celljump 1 *)
		(*Print["celljump axis 1: ",isAxis,x1];*)
		cntLS++;
		If[isAxis&&Not[MemberQ[cycle,x1]],
			AppendTo[cycle,x1]; x = x1,
			w = UpdateWeight[polyList, cnf, varList, x, w];
			{isDir, x1} = GradSearchAndApplyOp1[newPolyList,newCnf,newVarList, varInterval, x, w];  (* \:6cbf\:67d0\:4e9b\:65b9\:5411celljump 1 *)
			(*Print["celljump direction 1: ",isDir,x1];*)
			cntLS++;
			If[isDir&&Not[MemberQ[cycle,x1]],
				(*AppendTo[cycle,x1];*) x = x1,
				w = UpdateWeight[polyList, cnf, varList, x, w];
				{isAxis, x1} = SearchAndApplyOp2[polyList, cnf, varList, x, w]; (* \:6cbf\:5750\:6807\:8f74celljump 2 *)
				If[mcsat,Return[{"sat","ELS"(*,cntLS*)}]];
				cntLS++;
				(*Print["celljump axis 2: ",isAxis,x1];*)
				If[isAxis&&Not[MemberQ[cycle,x1]], 
				    AppendTo[cycle,x1]; x = x1, 
				    w = UpdateWeight[polyList, cnf, varList, x, w];
				    (*Print["w: ",w];*)
                    {isDir, x1} = GradSearchAndApplyOp2[polyList, cnf, varList, x, w]; (* \:6cbf\:67d0\:4e9b\:65b9\:5411celljump 2 *)
					(*Print["celljump direction 2: ",isDir,x1];*)
					x2=x;
				    If[Length[varList2]>=2,
						x2[varList2[[1]]]=x1[varList2[[1]]];
						x2[varList2[[2]]]=x1[varList2[[2]]],
						x2[varList2[[1]]]=x1[varList2[[1]]];
					];
					(*Print["celljump direction 2: ",isDir,x2];*)
				    If[MemberQ[cycle,x2],Return[{"unknown","ELS"}];];
				    If[isDir,
				        (*AppendTo[cycle,x2];*) x = x2,
				        (*w = UpdateWeight[polyList, cnf, varList, x, w];*)
				        Return[{"unknown","ELS"}];
					];
				];
			];
		];
	];
	Return[{"unknown","ELS"}];
];


(* ::Subsubsection:: *)
(*LSSolver*)
(*\:529f\:80fd\:ff1a\:6c42\:89e3SMT\:7684\:5c40\:90e8\:641c\:7d22\:6c42\:89e3\:5668\:ff0c\:4e24\:7ea7\:7b56\:7565\:662fLS\:7684celljump*)


LSSolver[polyList0_, cnf0_, varList_,lsLimit_,maxCntLS_]:=
Module[{cnt=1,init,lsInit={},ans,cons,consZero,polyList,cnf,LenDenNum,
		lnum,varnum,deg(*,cntELS,maxCntELS*), (*num, xnumTri,*)
		linearList, oneVarLinearList, preproc, newPolyList, newCnf, newVarList, varInterval, varFixList},
	
	cntLS=0;
    {linearList, oneVarLinearList} = OneVarLinearList[polyList0];
    (*Print["one var linear list: ", oneVarLinearList];
    Print["linear list: ", linearList];*)
	preproc = LSPreproc[polyList0, cnf0, varList, linearList, oneVarLinearList];
	(*Print["LS preprocessing: ", preproc];*)
	(*Switch[preproc,
		1, Return[{"sat", "LSPreprocessing"}], (*"error VarFixList: \:6240\:6709\:53d8\:91cf\:5747\:53d6\:56fa\:5b9a\:503c, \:516c\:5f0f\:53ef\:6ee1\:8db3."*)
		2, Return[{"unsat", "LSPreprocessing"}];(*"error: The CNF formula is unsatisfiable."*)
	];*)
	If[Length[preproc]==0,
		Switch[preproc,
			1, Return[{"sat", "LSPreprocessing"}], (*"error VarFixList: \:6240\:6709\:53d8\:91cf\:5747\:53d6\:56fa\:5b9a\:503c, \:516c\:5f0f\:53ef\:6ee1\:8db3."*)
			2, Return[{"unsat", "LSPreprocessing"}];(*"error: The CNF formula is unsatisfiable."*)
		];
	];
	If[preproc[[1]]==False,
		newPolyList =preproc[[2]];
		newCnf = preproc[[3]];
		newVarList = preproc[[4]];
		varInterval = preproc[[5]];
		,
		(*Return[{preproc[[1]],preproc[[2]],num,xnumTri,3}];*)
		Return[{"sat", "LSPreprocessing"}];
	];
	(*Print["varInterval: ",varInterval];*)
	
	While[cnt<=lsLimit,
		Which[cnt==1,
			(*Print["LS start: ",cnt];*)
			init=IniMethodZero[newVarList, varInterval];
			(*Print["init: ",init];*)
			AppendTo[lsInit,init];
			(*Print["LS start 1 input: ",
			{init,newPolyList,newCnf,newVarList,varInterval,cntLS,maxCntLS}];*)
			ans=LS[init,newPolyList,newCnf,newVarList,varInterval,maxCntLS];
            If[ans[[1]]!="unknown",(*Print["End time: ",SessionTime[]];*)Return[ans];];
			cnt++,
			cnt>=2&&cnt<=6,
			(*Print["LS start: ",cnt];*)
			init=IniMethodOne[newVarList, varInterval];
			(*init=Association[Map[#->RandomChoice[{-1,1}]&,varList]];*)
			If[Not[MemberQ[lsInit,init]],
                AppendTo[lsInit,init];
                ans=LS[init,newPolyList,newCnf,newVarList,varInterval,maxCntLS];
                If[ans[[1]]!="unknown",Return[ans];];
            ];
            cnt++,
            cnt>=7,
            (*Print["LS start: ",cnt];*)
            init=IniMethodTwo[varList, varInterval];
			(*init=Association[Map[#->RandomInteger[{-50*(cnt-6),50*(cnt-6)}]&,varList]];*)
            If[Not[MemberQ[lsInit,init]],
                AppendTo[lsInit,init];
                ans=LS[init,newPolyList,newCnf,newVarList,varInterval,maxCntLS];
                If[ans[[1]]!="unknown",Return[ans];];
            ];
            cnt++;
		];
	];

    (*Print["End time: ",SessionTime[]];*)

	Return[{"unknown","LS"}];
];


LS[x0_, polyList_, cnf_, varList_, varInterval_, maxCntLS_]:=
Module[{i, x, w, isAxis, x1, x2, isDir,
		cnt=1,init,lsInit={},(*maxCntLS,*)varListLast,vars=Length[varList],varList2,
		clauses,y,cons,consZero,cycle={},cad,mcsatPoly,LenDenNum,varnum=Length[varList]},
	(*Print["poly list: ",polyList];
	Print["cnf: ",cnf];
	Print["var list: ",varList];
	Print["var inv: ", varInterval];*)
	x = x0;
	w = Association[Table[cnf[[i]] -> 1, {i, Length[cnf]}]];
	(*Print["initial x: ", x];*)
	
	While[True,
		(*Print[SatCheck[polyList, cnf, varList, x]];*)
		If[SatCheck[polyList, cnf, varList, x],Return[{"sat","LS"}]];
		x1=x;
		(*Print["cntLS=",cntLS," maxCntLS=",maxCntLS];*)
		If[cntLS>maxCntLS,
		    cad=GenericCylindricalDecomposition[And@@Table[Or@@Table[If[cnf[[i,j,2]]<0,polyList[[cnf[[i,j,1]]]]<0,polyList[[cnf[[i,j,1]]]]>0],{j,Length[cnf[[i]]]}],{i,Length[cnf]}],varList];
            If[Length[cad[[1]]]==0 && Length[cad[[2]]]==0 && cad=={False,False},
                Return[{"unsat","openCAD"}],
                (*Return[{"CAD: sat",FindInstance[cad[[1]],varList]}];*)
                Return[{"sat","openCAD"}];
            ];
        ];
        i=0;
		While[i<varnum,
			i++;
			(*If[MemberQ[varFixList, i], Continue[];];*)
			If[Max[IntegerLength[Denominator[x1[[i]]]],IntegerLength[Abs[Numerator[x1[[i]]]]]]>15,
				(*Print["simplify"];*)
				LenDenNum=Min[IntegerLength[Denominator[x1[[i]]]],IntegerLength[Abs[Numerator[x1[[i]]]]]];
				x1[[i]]=IntegerPart[Numerator[x1[[i]]]/10^(LenDenNum-2)]/IntegerPart[Denominator[x1[[i]]]/10^(LenDenNum-2)];
			];
			If[IntegerLength[Denominator[x1[[i]]]]>5,x1[[i]]=0;];
		];
        
        cntLS++;
        (*Print["cntLS: ",cntLS];*)
        (*Print[polyList, cnf, varList, varInterval, varFixList, x, w];*)
		{isAxis, x1} = SearchAndApplyOp1[polyList, cnf, varList, varInterval, (*varFixList,*) x, w]; (* \:6cbf\:5750\:6807\:8f74celljump 1 *)
		(*Print["celljump axis 1: ",isAxis,x1];*)
		If[isAxis&&Not[MemberQ[cycle,x1]], AppendTo[cycle,x1]; x = x1,
			w = UpdateWeight[polyList, cnf, varList, x, w];
            cntLS++;
            (*Print["cntLS: ",cntLS];*)
			{isDir, x1} = GradSearchAndApplyOp1[polyList, cnf, varList, varInterval, (*varFixList,*) x, w]; (* \:6cbf\:67d0\:4e9b\:65b9\:5411celljump 1 *)
			(*Print["celljump direction 1: ",isDir,x1];*)
			If[MemberQ[cycle,x1],(*Print["cycle"];*)Break[]];
			If[isDir&&Not[MemberQ[cycle,x1]], AppendTo[cycle,x1]; x = x1,
                cntLS++;
                Break[];
			];
		];
	];
	Return[{"unknown","LS"}];
];


(* ::Subsubsection:: *)
(*MCSATSolver*)
(*\:529f\:80fd\:ff1a\:6c42\:89e3SMT\:7684MCSAT\:6c42\:89e3\:5668*)


MCSATSolver[Clause0_,F2_,X_]:=Module[{a,cc,i,j,xmap=<||>,fmap=<||>,F1,F,Flevel,Fnow,conflictstatelist,Ci,Cli,Clause,Clause1,Clearn={},
                varnum,Clausenum,assignment=Association[Map[#->0&,X]],lorder,z,lnum,ML,M,Morder,VC,
                Cstatus,Clstatus,levell,levelc,levelcl,level,tmplevel,tmpc,tmpcl,status,nowc,conflict,
                getFnow,getFlevel,getClause,checkconflict,Polynomialroot,getorder,addl,getF,
                samplecell,getsamplecell,nextsamplecell,cons,consZero,lenPoly},
    
    (*Print[Clause0];
    Print[F2];
    Print[X];*)
    (*Print["MCSATSolver: ",{Clause0,F2,X}];*)
    (*\:5904\:7406\:591a\:9879\:5f0f\:6052\:7b49\:4e8e\:5e38\:6570\:7684\:60c5\:5f62*)
    (*existPoly=Abs[Flatten[Clause0]];    
    Print[existPoly];  *) 
    lenPoly=Length[F2];     
    cons=Union[-1*Select[Range[lenPoly],Length[Variables[F2[[#]]]]==0&&F2[[#]]<0&],Select[Range[lenPoly],Length[Variables[F2[[#]]]]==0&&F2[[#]]>0&]];
	consZero=Select[Range[lenPoly],Length[Variables[F2[[#]]]]==0&&F2[[#]]==0&];
	(*Print[cons];*)
	Clause1=Table[If[Intersection[cons,Clause0[[i]]]=={},Clause0[[i]],Nothing],{i,Length[Clause0]}]/.Table[-cons[[i]]->Nothing,{i,Length[cons]}](*/.{}->Nothing*)/.Table[consZero[[i]]->Nothing,{i,Length[consZero]}]/.Table[-consZero[[i]]->Nothing,{i,Length[consZero]}];
	(*Print[Clause1];*)
	If[MemberQ[Clause1,{}]||Clause1=={},Return[{"unsat","There are constants that cannot be satisfied."}]];
	Clause=Clause1;
	F1=ReplacePart[F2, Table[Abs[cons[[i]]]->X[[1]],{i,Length[cons]}]];
	F1=ReplacePart[F1, Table[consZero[[i]]->X[[1]],{i,Length[consZero]}]];
	F=Map[{1,#}&,F1];	
	(*Print["Clause: ",Clause1];
	Print["F: ",F1];*)
                
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
