G:= GrigorchukGroup;
AssignGeneratorVariables(G);
Gp := Group(a*b*a*b,a*d*a*d,(b*a*d*a)^2,(a*b*a*d)^2);
Co := function(x,y)
	return x^-1*y^-1*x*y;
end;


IsCommuFinite := function(G,x)
	local g,h;
	for g in G do
		for h in G do
			if Co(g,h)=x then
				return true;
			fi;
		od;
	od;
	return false;
end;
IsCommuFinitebetter := function(G,x)
	local tbl,irr,s,g,h;
	tbl :=  CharacterTable(G);
	irr := Irr(tbl);
	s := Sum( irr, chi -> x^chi/(One(G)^chi) );
	return s<>0;
end;

SEARCH@FR.IsCommu := function(G,x)
	if not IsCommuFinitebetter(Range(G!.FRData.pi),x^G!.FRData.pi) then
		return false;
    elif ForAny(G!.FRData.sphere,s->ForAny(s,t->ForAny(G!.FRData.sphere,u->ForAny(u,v->Co(v,t)=x)))) then
        return true;
    fi;
    return fail;
end;

SEARCH@FR.IsCommuWitness := function(G,x)
	local s,t,u,v;
	for s in G!.FRData.sphere do
		for t in s do
			for u in G!.FRData.sphere do
				for v in u do
					if Co(t,v) = x then
						return [t,v];
					fi;
				od;
			od;
		od;
	od;
	return fail;
end;


SEARCH@FR.INIT(G);
IsCommu := function(G,x)
	local b;
    while true do
        b := SEARCH@FR.IsCommu(G,x);
        if b<>fail then return b; fi;
        while SEARCH@FR.EXTEND(G)=fail do
            Print("Fehler Commu");
        od;
        Info(InfoFR, 3, "IsCommu: searching at level ",G!.FRData.level," and in sphere of radius ",G!.FRData.radius);
    od;
end;
GetCommu := function(G,x)
	local b;
    while true do
        b := SEARCH@FR.IsCommuWitness(G,x);
        if b<>fail then return b; fi;
        while SEARCH@FR.EXTEND(G)=fail do
            Print("Fehler Commu");
        od;
        Info(InfoFR, 3, "IsCommu: searching at level ",G!.FRData.level," and in sphere of radius ",G!.FRData.radius);
    od;
end;
