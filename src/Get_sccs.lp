#show scc_atom/3.
#show scc_intern/2.

%#show check(C,A) : scc(C,X), literal_tuple(L,X), output(A,L).

scc_atom(C,X,A) :- scc(C,X), literal_tuple(L,X), output(A,L),
                    #count{Y : literal_tuple(L,Y)} 1.
scc_intern(C,X) :- scc(C,X), not scc_atom(C,X,_).