`M=[M_1;x_1->a[x_1];M_2;x_2->a[x_2];...;M_i;x_i->a[x_i];...];`
`M_i=[l1,l2,c|=l3,l4..,lk]`
```
(status,a,t)=2d-LS(F)
if status==SAT:
    return SAT 
level=0;
f_0={};
assignment=a;
M=[];
learn_clauses={};
fail_cells=t; #

for i in [1..n]:
    f_i=F\cup R[x_1,...,x_i] - f_{i-1};
while True:
    if f_{level}|M == SAT:
        if assignment[x_{level}] not in solve(M):
            assignment[x_{level}]= choose(M, x_{level});
        M = [M;x_{level}->assignment[x_{level}]];
        level++;
        if level>n:
            return SAT;
        if go_2d_ls? :
            (status,a,t)=2d-LS(F|assignment[x_1,...,x_{level}]);
            if status==SAT:
                return SAT;
            else:
                for i in [level+1..n]:
                    assignment[x_{i}]=a[x_{i}];
                fail_cells+=t; #
    else:        
        if \exist c in f_{level} such that c|M = UNSAT:
            status=(UNSAT,c);
        elif \exist c in  f_{level} such that c|M = unknown and only one of the literals l in c is unassigned:
            status=(P,l,c);
        elif:
            choose c in f_{level} such that c|M = unknown;
            choose l in c such that l|M = unknown;
            status=(D,l,c);
        if status[0]!=UNSAT:
            l=status[1];c=status[2];
            if solve(l,M)!={}:
                if status[0]==D:
                    M = [M; l];
                elif status[0]==P:
                    M = [M; c|=l];
            elif:
                min_clause = min conflict clause of  M and c;\
                cells = P_s(min_clause,assignment);
                lemma = ~cells \lor ~min_clause \lor ~l;
                learn_clauses = learn_clauses \cup {lemma};
                f_{level}= [f_{level}; lemma];
                M = [M; lemma|=~l];
                if status[0]!=D:
                    fail_cells+=1; #
                    status=(UNSAT,c);
        if status[0]==UNSAT:
            c=status[1];
            confilct = confilct clause of M and c in f_{level};
            learn_clauses = learn_clauses \cup {confilct};
            if x_{level} in  confilct:
                f_{level} = f_{level} \cup {confilct};
            else:
                tmp_level= max i of x_{i} in confilct;
                f_{tmp_level} = f_{tmp_level} \cup {confilct};
                level=tmp_level;

    if fail_cells > MAX_FAIL_CELLS: #
        return openCAD(F,learn_clauses);   
```
