InstallMethod(GrpWord, "(GrpWord) for a list of group elements and unknowns",
	[IsList,IsGroup],
	function(elms,G)
	local M,i;
		for i in elms do
			if not IsInt(i) then
				if not i in G then
					Error(i," must be an element of ", G);
				fi;
			fi;
		od;
		#TODO Simplify two group elements next to each other.
		M := Objectify(NewType(FamilyObj(G), IsGrpWord and IsGrpWordRep),
    rec(word := elms,
       group := G));
    return M;
	end
);

InstallMethod( GrpWordHom, "For a list of lists consisting of images",
	[IsList],
	function(L)
		if Length(L)=0 then
			Error("The list must contain at least one relation or called with a group as second argument.");
		fi;
		return Objectify(NewType(FamilyObj(Representative(L)),IsGrpWordHom and IsGrpWordHomRep),
		rec(rules := L));
	end
);

InstallOtherMethod( GrpWordHom, "For a list of lists consisting of images and a Group",
	[IsList,IsGroup],
	function(L,G)
		local fam;
		if Length(L)=0 then
				fam := NewType(FamilyObj(G),IsGrpWordHom and IsGrpWordHomRep);
		else 
				fam := NewType(FamilyObj(Representative(L)),IsGrpWordHom and IsGrpWordHomRep);
		fi;
		return Objectify(fam,rec(rules := L));
	end
);
InstallMethod( \=,  "for two GrpWordHoms",
		IsIdenticalObj,
    [ IsGrpWordHom and IsGrpWordHomRep, IsGrpWordHom and IsGrpWordHomRep ],
    function( x, y )
			return x!.rules = y!.rules;
		end 
);
	
InstallMethod( PrintObj,   "for GrpWords)",
   [ IsGrpWord and IsGrpWordRep ],
    function( x )
			local s,i,w;
			w := x!.word;
			s := Concatenation("Group word of length ",String(Length(w)));
    	Print(s);
	   end 
);

InstallMethod( PrintObj,   "for GrpWordHoms)",
	[ IsGrpWordHom and IsGrpWordHomRep ],
	function( x )
		local w;
		w := x!.rules;
		if Number(w)=0 then			
			Print("Trivial Group word Homomorphism");
		else
			Print("Group word Homomorphism on ",String(Number(w))," generators");
		fi;
  end 
);

InstallMethod( \=,  "for two GrpWords",
		IsIdenticalObj,
    [ IsGrpWord and IsGrpWordRep, IsGrpWord and IsGrpWordRep ],
    function( x, y )
			#TODO Ignore different Placeholders
			x := GrpWordCyclReducedForm(x);
			y := GrpWordCyclReducedForm(y);
			return x!.word = y!.word and y!.group = x!.group; 
		end 
);

InstallMethod( \*,   "for two GrpWords",
		IsIdenticalObj,
    [ IsGrpWord and IsGrpWordRep, IsGrpWord and IsGrpWordRep ],
    function( x, y )
    	return GrpWord(Concatenation(x!.word,y!.word),x!.group);
    end 
);

InstallMethod(InverseOp, "for a GrpWord",
	[IsGrpWord],
	function(x)
		local f;
		f := function(y) 
			if IsInt(y) then
				return -y;
			fi;
			return y^-1;
		end;
		return GrpWord(Reversed(List(x!.word,f)),x!.group);
	end
);

InstallMethod(OneOp, "for a GrpWord",
    [IsGrpWord],
     x -> GrpWord([],x!.group) 
);
InstallOtherMethod(\[\], "for a GrpWord",
	[IsGrpWord,IsInt],
	function(w,i) 
		return GrpWord([w!.word[i]],w!.group);
	end);

InstallOtherMethod(\[\], "for a GrpWord",
	[IsGrpWord,IsList],
	function(w,i) 
		return GrpWord(w!.word{i},w!.group);
	end);

InstallMethod(ImageOfGrpWordHom, "for a GrpWordHom and a GrpWord",
	[IsGrpWordHom,IsGrpWord],
	function(H,e)
		local res,x,h;
		res:=[];
		H := H!.rules;
		for x in e!.word do
			if IsPosInt(x) and IsBound(H[x]) then
				Append(res,H[x]!.word);
			elif IsInt(x) and IsPosInt(-x) and IsBound(H[-x]) then
				h := H[-x]^-1;
				Append(res,h!.word);
			else
				Add(res,x);
			fi;
		od;
		return GrpWord(res,e!.group);
	end
);	
InstallMethod( \*,   "for two GrpWordHoms",
		IsIdenticalObj,
    [ IsGrpWordHom and IsGrpWordHomRep, IsGrpWordHom and IsGrpWordHomRep ],
    function( x, y )
			local res,i;
			res:= [];
			for i in [1..Maximum(Length(x!.rules),Length(y!.rules))] do
				if IsBound(y!.rules[i]) then
					res[i] := ImageOfGrpWordHom(x,y!.rules[i]);
				elif IsBound(x!.rules[i]) then
					res[i] := x!.rules[i];
				fi;
			od;
			return GrpWordHom(res);
    end 
);
InstallMethod(OneOp, "for a GrpWordHom",
    [IsGrpWordHom],
     x -> GrpWordHom([],x!.group) 
);
InstallMethod(UnknownsOfGrpWord, "for a GrpWord",
	[IsGrpWord],
	w -> Filtered(w!.word,IsInt)
);
InstallMethod(LengthOfGrpWord, "for a GrpWord",
	[IsGrpWord],
	w -> Length(w!.word)
);

InstallMethod(IsSquareGrpWord, "for a GrpWord",
		[IsGrpWord],
		function(w)
			local i,Val;
			Val := rec();
			for i in UnknownsOfGrpWord(w) do
				i := AbsInt(i);
				if IsBound(Val.(i)) then
					if Val.(i) > 1 then
						return false;
					fi;
					Val.(i) := 2;	
				else
					Val.(i) := 1;
				fi;
			od;
			return true;
		end
);

InstallMethod(IsOrientedGrpWord, "for a square GrpWord",
	[IsSquareGrpWord],
	function(w)
		local i,Val;
		w := UnknownsOfGrpWord(w);
		if Length(w) = 0 then
			return true;
		fi;
		Val := ListWithIdenticalEntries( Maximum(-1*Minimum(w),Maximum(w)), 0 );
		for i in w do
			Val[AbsInt(i)] := Val[AbsInt(i)] + i;
		od;
		if not Sum(Val) = 0 then
			return false;
		fi;			
		return true;	
	end
);

InstallMethod(GrpWordReducedForm, "for a Grpword",
	[IsGrpWord],
	function(x)
		local i,lastType,lastUnknown,change,w,L;
		w := x!.word;
		change := true;
		while (change) do
			change := false;
			lastType := 0; #0for unknown, 1 for constant
	  	lastUnknown :=0;
			L := [];
			for i in w do 
				if IsInt(i) then
					if not lastType =0 or lastUnknown <> -i then
						Add(L,i);
						lastType := 0;
						lastUnknown := i;
					fi;
				else 
					if not IsOne(i) then
						if lastType = 1 then
							L[Length(L)] := L[Length(L)]*i;
							change := true;
						else 
							Add(L,i);
						fi;
						lastType := 1;
					fi;
				fi;
			od;
			w := L;
		od;
		L := w;
		w := GrpWord(L,x!.group);
		IsSquareGrpWord(w);
		IsOrientedGrpWord(w);
		return w;		
	end
);
InstallMethod(GrpWordCyclReducedForm, "for a Grpword",
	[IsGrpWord],
	function(x)
		local L;
		x := GrpWordReducedForm(x);
		L := x!.word;
		#Check if word begins with constant
		if Length(L) > 1 and not IsInt(L[1]) then
			if IsInt(L[Length(L)]) then
				Add(L,L[0]);
			else
				L[Length(L)] := L[Length(L)]*L[1];
				if IsOne(L[Length(L)]) then #kill last entry
					L := L{[1..Length(L)-1]};
				fi;
			fi;#kill first entry
			L:= L{[2..Length(L)]};
		else
			return x;
		fi;
		x := GrpWord(L,x!.group);
		IsSquareGrpWord(x);
		IsOrientedGrpWord(x);
		return x;		
	end
);
NormalForm := function(x)
	local w,i,Hom,Word,N;
	#Print("..Todo: Word ",x!.word,"\n");
	x:= GrpWordReducedForm(x);
	w:= x!.word;
	if Length(w)<3 then
		return [x,GrpWordHom([],x!.group)];
	fi;
	if not IsInt(w[1]) then
		#x is reduced so w[2] is Integer
		Hom := [];
		if w[2]<0 then
			Hom[-w[2]] := GrpWord([-w[2],w[1]],x!.group);
		else
			Hom[w[2]] := GrpWord([w[1]^-1,w[2]],x!.group);
		fi;
		Hom := GrpWordHom(Hom);
		N := NormalForm(ImageOfGrpWordHom(Hom,x));
		return [N[1],N[2]*Hom];
	fi;
	if IsOrientedGrpWord(x) then
		if IsInt(w[3]) and w[1] = -w[3] and w[1]<0 then
			N := NormalForm(x[[4..LengthOfGrpWord(x)]]);
			return [x[[1..3]]*N[1],N[2]];
		elif w[1] = -w[3] then
			if Length(w)>3 then
				N := NormalForm(x[[4..LengthOfGrpWord(x)]]);
			else
				N := [GrpWord([],x!.group),GrpWordHom([],x!.group)];
			fi;
		  Hom := [];
			Hom[w[1]] := GrpWord([w[3]],x!.group);
			Hom := GrpWordHom(Hom);
			#Print("...Hom: ",Hom!.rules[w[1]]!.word,"\n");
			return [ImageOfGrpWordHom(Hom,x[[1..3]])*N[1],Hom*N[2]];
		fi;		
	fi;
	Print ("abort here");
	return [GrpWord([],x!.group),GrpWordHom([],x!.group)];
end;

NormalForm2:= function(xx)
	local case10,case11a,case11b,case2a,case2b,vfind,i,j,t,x,vlen,v,w,v1,v2,w1,w2,w11,w12,w21,w22,first,Hom,Hom2,y;
	xx:= GrpWordReducedForm(xx);
	w:= xx!.word;
	if Length(w)<3 then
		return [xx,GrpWordHom([],xx!.group)];
	fi;
	#Functions for Oriented GrpWords:
	case10 := function(w1,v,w2,x,G)
		local N,Hom,h,c;
		N := NormalForm2(GrpWord(Concatenation(w1,w2),G));
		h := N[1]!.word;
		if IsInt(h[Length(h)]) then
			Hom := [];
			Hom[x] := GrpWord([x],G)*GrpWord([w2])^-1;
			return [N[1]*GrpWord(Concatenation(h,[-x,v,x]),G),GrpWordHom(Hom)*N[2]];
		else
			c:= h[Length(h)];
			Hom := [];
			Hom[x] := GrpWord([x,c],G)*GrpWord([w2])^-1;
			return [N[1][[1..Length(h)-1]]*GrpWord(Concatenation(h,[-x,v,x,c]),G),GrpWordHom(Hom)*N[2]];
		fi;
	end;
	if IsOrientedGrpWord(xx) then
		#Find x s.t. w=w1 -x v x w2 with |v| minimal
		t:= rec();
		for i in w do
			if IsInt(i) then
				i:= AbsInt(i);
				if IsBound(t.(i)) then
					t.(i) := -t.(i);
				else
					t.(i) := 0;
				fi;
			fi;
			for j in RecNames(t) do
				if t.(j)>=0 then
					t.(j) := t.(j) +1;
				fi;
			od;
		od;
		#counting done
		Print("Counting dict: ",t,"\n");
		x := 0;
		vlen := -Length(w);
		for i in RecNames(t) do
			if t.(i)>vlen then
				x := i;
				vlen := t.(i);
			fi;
		od;
		x := Int(x);
		Print("Shortest word is of length ",vlen," and surounded by ",String(x),"\n");
		#Minimal i found;
		first := true;
		toInvert := false;
		for i in [1..Length(w)] do
			if IsInt(w[i]) and AbsInt(w[i]) = x then
				if first then
					if w[i]>0 then
						toInvert := true;
					fi;
					w1 := w{[1..i-1]};
					first := false;
					j:= i+1;
				else 
					v:= w{[j..i-1]};
					if i<Length(w) then
						w2 := w{[i+1..Length(w)]};
					else
						w2 := [];
					fi;
					break;
				fi;
			fi;
		od;
		Hom := [];
		if toInvert then
			Hom[x] := GrpWord([-x],xx!.group);
		fi;
		Hom := GrpWordHom(Hom,xx!.group);
		Print("Word decomposes to ",[w1,-x,v,x,w2],"\n");
		#Decomposition done
		if Length(v)=1 then #Case 1
			v := v[1];
			if IsInt(v) then #Case 1.1
				if v<0 then
					Hom2 := []:
					Hom2[-v] := GrpWord([v],xx!.group);
					Hom := GrpWordHom(Hom2)*Hom;
					v := -v;
				fi;
				i := Position(w1,-v);
				if not i = fail then #Case 1.1.a
					w11 := w1{[1..i-1]};
					w12 := w1{[i+1..Length(w1)]};
					return case11a(w11,w12,v,w2,x);
				else #Case 1.1.b
					i := Position(w2,-v);
					if i = fail then 
						Error("Strange Error");
					fi;
					w21 := w2{[1..i-1]};
					w22 := w2{[i+1..Length(w2)]};
					return case11b(w1,v,w21,w22,x);
				fi;
			else #Case 1.0
				return case10(w1,v,w2,x);
			fi;
		else #Case 2
			y := 0;
			for i in v do
			if IsInt(i) then
				y := i;
				if i<0 then
					break
				fi;
			fi;
			od;
			i := Position(v,y);
			if y>0 then
				Hom2 := []:
				Hom2[y] := GrpWord([-y],xx!.group);
				Hom := GrpWordHom(Hom2)*Hom;
				y := -y;
			fi;
			y := -y;
			v1 := v{[1..i-1]};
			v2 := v{[i+1..Length(v)]};
			i := Position(w1,y);
			if not i = fail then #Case 2.a
				w11 := w1{[1..i-1]};
				w12 := w1{[i+1..Length(w1)]};
				N := case11a(w11,Concatenation(v2,v1),x,Concatenation(w12,w2),y);
				Hom2 := [];
				Hom2[x] :=GrpWord(v2,xx!.group)^-1*GrpWord(Concatenation([x,y],w12),xx!.group);
				return [N[1],N[2]*GrpWordHom(Hom2)*Hom];
			else #Case 2.b
				i := Position(w2,y);
				if i = fail then 
					Error("Strange Error");
				fi;
				w21 := w2{[1..i-1]};
				w22 := w2{[i+1..Length(w2)]};
				N := case11a(Concatenation(w1,w21),Concatenation(v2,v1),x,w22,y);
				Hom2 := [];
				Hom2[x] := GrpWord(v2,xx!.group)^-1*GrpWord([x],xx!.group)*GrpWord(w21,xx!.group)^-1;
				return [N[1],N[2]*GrpWordHom(Hom2)*Hom];
			fi;
		fi; #End Case 2
	fi; #End Oriented Case	
end;
