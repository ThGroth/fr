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
		if w[1] = -w[3] and w[1]<0 then
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
;
	
end;
