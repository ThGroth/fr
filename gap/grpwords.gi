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

InstallMethod( PrintObj,   "for GrpWords)",
   [ IsGrpWord and IsGrpWordRep ],
    function( x )
			local s,i,w;
			w := x!.word;
			s := Concatenation("Group word of length ",String(Length(w)));
    	Print(s);
	   end 
);

InstallMethod( \=,  "for two GrpWords",
		IsIdenticalObj,
    [ IsGrpWord and IsGrpWordRep, IsGrpWord and IsGrpWordRep ],
    function( x, y )
			#TODO Ignore different Placeholders.
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

InstallMethod(OneOp, "for a GrpWord",
    [IsGrpWord],
     x -> GrpWord([],x!.group) 
);

InstallMethod(UnknownsOfGrpWord, "for a GrpWord",
	[IsGrpWord],
	w -> Filtered(w!.word,IsInt)
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
		w := UnknowmsOfGrpWord(w);
		Val := ListWithIdenticalEntries( Maximum(-1*Minimum(w),Maximum(w)), 0 );
		for i in w do
			Val[AbsInt(i)] := Val[AbsInt(i)] + i;
		od;
		if not Sum(L) = 0 then
			return false;
		fi;			
		return true;	
	end
);

ReducedForm := function(x)
	local i,last,w,L;
	w := x!.word;
	last_in_grp := 0;
	L := [];
	for i in w do
		if IsInt(i) then
			Add(L,i);
			last_in_grp := 0;	
		else 
			if last_in_grp = 1 then
				L[Length(L)] := L[Length(L)]*i;
			else 
				Add(L,i);
			fi;
			last_in_grp := 1;
		fi;
	od;
	return GrpWord(L,x!.group);		
end; 
NormalForm := function(w)
	if IsOrientedGrpWord(w) then
		;				
	
	fi;
	return false;
	
end;
