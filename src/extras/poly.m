 
LUnruleH[Rule[x_,y_]]:=y
LUnruleH[x_]:=x
LUnruleI[t_List] := Map[LUnruleH,t]
LUnrule[t_List] := Map[LUnruleI, t]