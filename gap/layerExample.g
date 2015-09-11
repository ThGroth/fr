a := MealyElement([[2,2,2,2,2],[2,2,2,2,2]],[(1,2,3,4,5),()],1);
b := MealyElement([[2,2,2,2,2],[2,2,2,2,2]],[(1,2,3),()],1);
al := MealyElement([[2,2,2,2,2],[2,2,2,2,2],[1,3,2,2,2]],[(1,2,3,4,5),(),()],3);
bl := MealyElement([[2,2,2,2,2],[2,2,2,2,2],[1,3,2,2,2]],[(1,2,3),(),()],3);

G := Group(a,b,al,bl);

inv := function(r)
	return FRGrpWord(List(Permuted(r!.states,r!.activity^-1),x->x^-1),r!.activity^-1,r!.group);
end;

Co := function(r,s)
	return inv(r)*inv(s)*r*s;
end;
F := FreeGroup(5);

#Begin Example
x := FRGrpWordUnknown(6,(1,2,3,4,5),G);
y := FRGrpWordUnknown(12,(1,2,3,4),G);

g := FRGrpWord(List(GeneratorsOfGroup(F),x->GrpWord([x],F)),(1,5,2),F);

w := Co(x,y)*g;
U := Uniquify(w!.states)[1];
N := List(U,x->GrpWordNormalForm(x)[1]);
#End Example

#Count of how many comutators a normal form contains.
GetGenus := function(w)
	local nwl, gen,i;
	nwl := GrpWordNormalForm(w)[1]!.word;
	gen := 0;
	while Length(nwl)-4*gen >= 4 do
		if ForAll(nwl{[4*gen+1..4*gen+4]},IsInt) then
			if nwl[4*gen+1] = - nwl[4*gen+3] and nwl[4*gen+2] = - nwl[4*gen+4] then
				gen := gen +1;
			else 
				break;
			fi;
		else 
			break;
		fi;
	od;
	return gen;
end;

#Count the occurencies of constants in a word
GetNbOfConstants := function(w)
	local nwl, i, elm;
	nwl := GrpWordNormalForm(w)[1]!.word;
	elm := One(F);
	for i in nwl do
		if not IsInt(i) then
			elm := elm * i;
		fi;
	od;
	return Length(elm);
end;
#Now Check again if all Group elements of G can be brought to a form with more commutators than constants-.

#Group elements of G can have the whole of  A_5
Check := function()
	local A5, act, g, Sig, sig,x,y,U,u,found,z,d,xt,yt;
	A5 := AlternatingGroup(5);
	for act in A5 do
		g := FRGrpWord(List(GeneratorsOfGroup(F),x->GrpWord([x],F)),act,F); 
		Sig := GrpWordSolve(GrpWord([-1,-2,1,2,act],A5));
		found := false;
		for sig in Sig do
			d := sig!.rules;
			xt := d[1]!.word;
			yt := d[2]!.word;
			if Length(xt)=0 then
				xt := [()];
			fi;
			if Length(yt)=0 then
				yt := [()];
			fi;
			x := FRGrpWordUnknown(6,xt[1],G); # x = <x7,x8,x9,x10,x11>sig_1
			y := FRGrpWordUnknown(12,yt[1],G); # x = <x13,x14,x15,x16,x17>sig_2
			w := Co(x,y)*g;
			U := Uniquify(w!.states)[1];
		#	for u in U do
		#		Print("Genus: ",GetGenus(u)," Constants: ",GetNbOfConstants(u)," ;; ");
		#	od;q
		#	Print("\n");
		#	if ForAny(U,z->GetNbOfConstants(z)=5) then
		#		Print(U);
		#	fi;
			if ForAll(U,z-> GetGenus(z)*2>GetNbOfConstants(z) or (GetGenus(z)*2>=GetNbOfConstants(z) and GetNbOfConstants(z)>2) then
				found := true;
				break;
			fi;
		od;
		if not found then
			Print("Problem finding something for ",act,"\n");
		else
			Print(act, " done!\n");
		fi;
	od;
end;

dN := function(g)
	if g in Nucleus(G) then
		return 0;
	else 
		return Maximum(List(Alphabet(g),i->dN(State(g,i))))+1;
	fi;
end;

IsoPhi := function(g,G)
	return FRGrpWord(List(Alphabet(g),x->GrpWord([State(g,x)],G)),Activity(g),G);
end;

co := function(x,y)
	return x^-1*y^-1*x*y;
end;
xa := a^2;
xal := al^2;
yal := bl^2*xal*bl^2*xal^2*bl^2*xal;
xb := a^3;
xbl :=al^3;
ybl := bl^2*al^2*bl^2*al;
z := b^2*a^2*(b^2*a^4)^2;
sal:=co(xal,z^-1*yal*z)^(a^4); #<al,1,1,1,1>()
sa:=(al^-1*sal^a)^-1; #<a,1,1,1,1>()
sbl:=co(xbl,z^-1*ybl*z)^(a^4); #<bl,1,1,1,1>()
sb:=(bl^-1*sbl^a)^-1; #<b,1,1,1,1>()

g := sal*sa^a*sbl^(a^2)*sb^(a^3)*sbl^(a^4); # <al,a,bl,b,bl>()

N := Group(a,b);
M := Group(al,bl);


hom:=EpimorphismFromFreeGroup(G);
inGen := function(g)
	local w,x;
	w:=PreImagesRepresentative(hom,g);
	return List([1..Length(w)],x->Subword(w,x,x)^hom);
end;


#x --> <x,1,1,1,1>()
inState := function(x)
	local L,g,y;
	L := inGen(x);
	g := One(x);
	for y in L do
		if y = a then
			g := g*sa;
		elif  y = b  then
			g := g*sb;
		elif  y = al then
			g := g*sal;
		elif  y = bl  then
			g := g*sbl;
		elif y = a^-1 then
			g := g*sa^-1;
		elif  y = b^-1  then
			g := g*sb^-1;
		elif  y = al^-1 then
			g := g*sal^-1;
		elif  y = bl^-1  then
			g := g*sbl^-1;	
		else
			Print("Strange Error here...");
		fi;
	od;
	return g;
end;

d1 := al*a;
d2 := al*a*al;
d3 := al*a^-1*al^-1*a*al;

