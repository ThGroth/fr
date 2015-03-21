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
				end);

InstallMethod( PrintObj,   "for GrpWords)",
   [ IsGrpWord and IsGrpWordRep ],
    function( x )
			local s,i,w;
			w := x!.word;
			s := Concatenation("Group word of length ",String(Length(w)));
    	Print(s);
	   end );

InstallMethod( \=,  "for two GrpWords",
		IsIdenticalObj,
    [ IsGrpWord and IsGrpWordRep, IsGrpWord and IsGrpWordRep ],
    function( x, y )
			#TODO Ignore different Placeholders.
			return x!.word = y!.word and y!.group = x!.group; 
		end );

InstallMethod( \*,   "for two GrpWords",
		IsIdenticalObj,
    [ IsGrpWord and IsGrpWordRep, IsGrpWord and IsGrpWordRep ],
    function( x, y )
    	return GrpWord(Concatenation(x!.word,y!.word),x!.group);
    end );

InstallMethod(OneOp, "for a GrpWord",
    [IsGrpWord],
     x -> GrpWord([1],x!.group) 
		 );
