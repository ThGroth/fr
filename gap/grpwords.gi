##### Temporary Things #############################################
G := GrigorchukGroup;
AssignGeneratorVariables(G);
#x := GrpWord([1,-5,a,5,b,-1,-2,3,a,4,-3,b,-4,c,2],G);
########################################################################################
####                                                                                ####
####                              Constructors	                                    ####
####                                                                                ####
########################################################################################

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
		M := Objectify(NewType(FamilyObj(G), IsGrpWord and IsGrpWordRep),
    rec(word := elms,
       group := G));
    return M;
	end
);

InstallMethod(GrpWordDecomposable, "for a groupWord",
	[IsGrpWord],
	function(w)
	local M,i,d,G,Hom;
		G := w!.group;
		if not IsFRGroup(G) then
			TryNextMethod();
		fi;
		d := Length(AlphabetOfFRSemigroup(G));
		Hom := [];
		for i in UnknownsOfGrpWord(w) do
			Hom[AbsInt(i)] := GrpWord([(d+1)*AbsInt(i)],G);
		od;
		Hom := GrpWordHom(Hom,G);
		M := Objectify(NewType(FamilyObj(G), IsGrpWord and IsGrpWordDecomposableRep),
					rec(word := ImageOfGrpWordHom(Hom,w)!.word,
							group := w!.group,
							hom := Hom));
    return M;
	end
);

InstallMethod( GrpWordHom, "For a list of lists consisting of images",
	[IsList],
	function(L)
		if Length(L)=0 then
			Error("The list must contain at least one relation or called with a group or family as second argument.");
		fi;
		return Objectify(NewType(FamilyObj(Representative(L)),IsGrpWordHom and IsGrpWordHomRep),
		rec(rules := L));
	end
);

InstallOtherMethod( GrpWordHom, "For a list of lists consisting of images and a Group",
	[IsList,IsGroup],
	function(L,G)
		local fam;
		fam := NewType(FamilyObj(G),IsGrpWordHom and IsGrpWordHomRep);
		return Objectify(fam,rec(rules := L));
	end
);
InstallOtherMethod( GrpWordHom, "For a list of lists consisting of images and a Family",
	[IsList,IsFamily],
	function(L,F)
		local fam;
		fam := NewType(F,IsGrpWordHom and IsGrpWordHomRep);
		return Objectify(fam,rec(rules := L));
	end
);

InstallMethod(FRGrpWord, "For a list of grpwords, a permutation and an FRGroup",
	[IsList,IsPerm,IsFRGroup],
	function(L,p,G)
		local M;
		M := Objectify(NewType(FamilyObj(G), IsFRGrpWord and IsFRGrpWordStateRep),
					rec(states := L,
							group := G,
							activity := p));
    return M;	
	end
);

InstallMethod(FRGrpWordUnknown, "For an integer, a permutation and an FRGroup",
	[IsInt, IsPerm, IsFRGroup],
	function(i,p,G)
		local d,L,M;
		d := Length(AlphabetOfFRSemigroup(G));
		if i mod (d+1) <> 0 then
			Error("The first Argument must be a valid decomposable variable");
		fi;
		if i>0 then
			L :=List([i+1..i+d],x->GrpWord([x],G));
			return FRGrpWord(L,p,G);
		else
			L := List([-i+1..-i+d],x->GrpWord([-x],G)); 
			return FRGrpWord(Permuted(L,p^-1),p^-1,G);
		fi;
	end
);

######################################################################################
####                                                                              ####
####                               Standard Methods                               ####
####                                                                              ####
######################################################################################
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
InstallMethod( PrintObj,   "for FRGrpWords)",
	[ IsFRGrpWord and IsFRGrpWordStateRep ],
	function( x )
		local i,j, res,first;
		first := true;
		Print("<");
		for i in x!.states do
			if not first then
				Print(",");
			else
				first := false;
			fi;
			for j in i!.word do
				if IsInt(j) then
					Print(j);
				elif HasName(j) then
					Print(Name(j));
				else
					Print("gc");
				fi;
			od;
		od;
		Print(">",x!.activity);
  end 
);
InstallMethod( \=,  "for two GrpWords",
		IsIdenticalObj,
    [ IsGrpWord and IsGrpWordRep, IsGrpWord and IsGrpWordRep ],
    function( x, y )
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
			return GrpWordHom(res,FamilyObj(x));
    end 
);
InstallMethod( \*,   "for two FRGrpWords",
		IsIdenticalObj,
	 [ IsFRGrpWord and IsFRGrpWordStateRep, IsFRGrpWord and IsFRGrpWordStateRep ],
    function( x, y )
   		local L,i;
			L := [];
			for i in [1..Length(x!.states)] do
				Add(L,x!.states[i]*y!.states[i^x!.activity]);
			od;
			return FRGrpWord(L,x!.activity * y!.activity,y!.group);
    end 
);
InstallMethod( \*,   "for an FRElement and a FRGrpWord",
	 [ IsFRElement, IsFRGrpWord and IsFRGrpWordStateRep ],
    function( x, y )
   		local L,i;
			L := DecompositionOfFRElement(x);
			for i in [1..Length(L[1])] do
				L[1][i] := GrpWord([L[1][i]],y!.group)*y!.states[L[2][i]];
			od;
			return FRGrpWord(L[1],Activity(x) * y!.activity,y!.group);
    end 
);
InstallMethod( \*,   "for an FRGrpWord and an FRElement",
	 [IsFRGrpWord and IsFRGrpWordStateRep, IsFRElement ],
    function( x, y )
   		local L,S,i;
			L := DecompositionOfFRElement(y);
			S := [];
			for i in [1..Length(x!.states)] do
				Add(S, x!.states[i] * GrpWord([L[1][i^x!.activity]],x!.group));
			od;
			return FRGrpWord(S,x!.activity*Activity(y),x!.group);
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
		#return GrpWord(res,e!.group);
		return GrpWordReducedForm(GrpWord(res,e!.group));
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
		return ForAll(Val,x->x=0);
	end
);

InstallMethod(GrpWordReducedForm, "for a Grpword in GrpWord representation",
	[IsGrpWord and IsGrpWordRep],
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
					if lastType = 0 and lastUnknown = -i then
						Unbind(L[Length(L)]);
						#Print("Remove L[",Length(L),"] Now L:",L,"\n");
						lastUnknown := 0;
						change := true;
					elif lastType = 1 or lastUnknown <> -i then
						Add(L,i);
						#Print(i,"added\nNow L:",L,"\n");
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
						#	Print(i,"added\nNow L:",L,"\n");
						fi;
						lastType := 1;
					fi;
				fi;
			od;
			w := L;
			#Print("Reducing.. Now ",w,"\n");
		od;
		L := w;
		w := GrpWord(L,x!.group);
		if IsSquareGrpWord(w) then
			IsOrientedGrpWord(w);
		fi;
		return w;		
	end
);
InstallMethod(GrpWordReducedForm, "for a Grpword in FRGrpWord representation",
	[IsGrpWord and IsFRGrpWordStateRep],
	function(x)
		local s,L;
		L := [];
		for s in x!.states do	
			Add(L,GrpWordReducedForm(s));
		od;
		return FRGrpWord(L,x!.activity,Representative(x!.states)!.group);		
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

InstallMethod(GrpWordNormalForm, "for a Grpword",
	[IsGrpWord],
	function(x)
		local NormalForm2;
		NormalForm2:= function(xx)
			local case10,case11a,case11b,case3,toInvert,vfind,i,j,t,x,vlen,v,w,v1,v2,w1,w2,w11,w12,w21,w22,w3,first,Hom,Hom2,y,N;
			Print("Call of NormalForm2¸with");
			View(xx!.word);
			Print("\n");
			xx:= GrpWordReducedForm(xx);
			w:= xx!.word;
			#Functions for Oriented GrpWords:
			# w = w1·x⁻·v·x·w2
			case10 := function(w1,v,w2,x,G)
				local N,Hom,h,c;
				#Print("Case 10:");
				#View([w1,v,w2,x]);
				#Print("\n");
				N := NormalForm2(GrpWord(Concatenation(w1,w2),G));
				h := N[1]!.word;
				Hom := [];
				Hom[x] := GrpWord([x],G)*GrpWord(w2,G)^-1;
				if Length(h)=0 then
					return [GrpWord([-x,v,x],G),GrpWordHom(Hom)];
				fi;
				#Does N end with a constant?
				if IsInt(h[Length(h)]) then
					return [N[1]*GrpWord([-x,v,x],G),N[2]*GrpWordHom(Hom)];
				else
					c:= h[Length(h)];
					Hom := [];
					Hom[x] := GrpWord([x,c],G)*GrpWord(w2,G)^-1;
					return [N[1][[1..Length(h)-1]]*GrpWord([-x,v,x,c],G),N[2]*GrpWordHom(Hom)];
				fi;
			end;
			# w = w11·v⁻·w12·x⁻·v·x·w2
			case11a := function(w11,w12,v,w2,x,G)
				local N,Hom,h;
				#Print("Case 11a:");
				#View([w11,w12,v,w2,x]);
				#Print("\n");
				N := NormalForm2(GrpWord(Concatenation(w11,w12,w2),G));
				Hom := [];
				h := GrpWord(w11,G);
				Hom[x] := h^-1*GrpWord(Concatenation([x],w11,w12),G);
				Hom[v] := h^-1*GrpWord(Concatenation([v],w11),G);
				return [GrpWord([-v,-x,v,x],G)*N[1],N[2]*GrpWordHom(Hom)];
			end;
			# w = w1·x⁻·v·x·w21·v⁻·w22
			case11b := function(w1,v,w21,w22,x,G)
				local N,Hom,h;
				#Print("Case 11b:");
				#View([w1,v,w21,w22,x]);
				#Print("\n");
				N := NormalForm2(GrpWord(Concatenation(w1,w21,w22),G));
				Hom := [];
				Hom[x] := GrpWord(Concatenation(w1,w21),G)^-1 *GrpWord(Concatenation([x],w1),G);
				Hom[v] := GrpWord(Concatenation(w1,w21),G)^-1 *GrpWord(Concatenation([-v],w1,w21),G);
				return [GrpWord([-x,-v,x,v],G)*N[1],N[2]*GrpWordHom(Hom)];
			end;
			# w = x²·w2
			case3 := function(x,w2,G)
				local N,N2,Hom,y,z;
				#Print("Case 3:");
				#View([x,w2]);
				#Print("\n");
				N := NormalForm2(GrpWord(w2,G));
				#Check if N start with [y,z]
				if Length(N[1]!.word)<4 or not IsInt(N[1]!.word[2]) or N[1]!.word[1]=N[1]!.word[2] then
					#Print("End is Ok.. leaving Case 3\n");
					return [GrpWord([x,x],G)*N[1],N[2]];
				else
					#Print("w2 contains commutator...\n");
					y := N[1]!.word[3];
					z := N[1]!.word[4];
					Hom := [];
					Hom[x] := GrpWord([x,y,z],G);
					Hom[y] := GrpWord([-z,-y,-x,y,z,x,y,z],G);
					Hom[z] := GrpWord([-z,-y,-x,z],G);
					N2 := case3(z,N[1]!.word{[5..Length(N[1]!.word)]},G);
					return [GrpWord([x,x,y,y],G)*N2[1],GrpWordHom(Hom)*N2[2]*N[2]];
				fi;
			end;
			if IsOrientedGrpWord(xx) then
				if Length(w)<3 then
					return [xx,GrpWordHom([],xx!.group)];
				fi;
				#Print("Oriented");
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
				#Print("Counting dict: ",t,"\n");
				x := 0;
				vlen := -Length(w);
			for i in RecNames(t) do
				if t.(i)>vlen then
					x := i;
					vlen := t.(i);
				fi;
			od;
			x := Int(x);
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
			#Decomposition done
			if Length(v)=1 then #Case 1
				v := v[1];
				if IsInt(v) then #Case 1.1
					if v<0 then
						Hom2 := [];
						Hom2[-v] := GrpWord([v],xx!.group);
						Hom := GrpWordHom(Hom2)*Hom;
					fi;
					i := Position(w1,-v);
					if not i = fail then #Case 1.1.a
						w11 := w1{[1..i-1]};
						w12 := w1{[i+1..Length(w1)]};
						Display(N[2]!.rules[1]!.word);
						return [N[1],N[2]*Hom];
					else #Case 1.1.b
						i := Position(w2,-v);
						if i = fail then 
							Error("Strange Error");
						fi;
						w21 := w2{[1..i-1]};
						w22 := w2{[i+1..Length(w2)]};
						N:= case11b(w1,AbsInt(v),w21,w22,x,xx!.group);
						return [N[1],N[2]*Hom];
					fi;
				else #Case 1.0
					N := case10(w1,v,w2,x,xx!.group);
					return [N[1],N[2]*Hom];
				fi;
				else #Case 2
					#Print("Case2.");
					y := 0;
					for i in v do
					if IsInt(i) then
						y := i;
						if i<0 then
							break;
						fi;
					fi;
					od;
					i := Position(v,y);
					if y>0 then
						Hom2 := [];
						Hom2[y] := GrpWord([-y],xx!.group);
						Hom := GrpWordHom(Hom2)*Hom;
						y := -y;
					fi;
					y := -y;
					v1 := v{[1..i-1]};
					v2 := v{[i+1..Length(v)]};
					i := Position(w1,y);
					if not i = fail then #Case 2.a
						#Print("a. ");
						w11 := w1{[1..i-1]};
						w12 := w1{[i+1..Length(w1)]};
						N := case11a(w11,Concatenation(v2,v1),x,Concatenation(w12,w2),y,xx!.group);
						Hom2 := [];
						Hom2[x] :=GrpWord(v2,xx!.group)^-1*GrpWord(Concatenation([x,y],w12),xx!.group);
						return [N[1],N[2]*GrpWordHom(Hom2)*Hom];
					else #Case 2.b
						#Print("b. ");
						i := Position(w2,y);
						if i = fail then 
							Error("Strange Error");
						fi;
						w21 := w2{[1..i-1]};
						w22 := w2{[i+1..Length(w2)]};
						N := case11a(Concatenation(w1,w21),Concatenation(v2,v1),x,w22,y,xx!.group);
						Hom2 := [];
						Hom2[x] := GrpWord(v2,xx!.group)^-1*GrpWord([x],xx!.group)*GrpWord(w21,xx!.group)^-1;
						return [N[1],N[2]*GrpWordHom(Hom2)*Hom];
					fi;
				fi; #End Case 2
				else #so not oriented
					#Print("Nonoriented Case:\n");
					#find x s.t. w = w1·x·w2·x·w3
					t:= rec();
					for i in [1..Length(w)] do
						if IsInt(w[i]) then
						if IsBound(t.(w[i])) then
							x:= w[i];
							w1:= w{[1..t.(w[i])-1]};
							w2:= w{[t.(w[i])+1..i-1]};
						w3:= w{[i+1..Length(w)]};
						break;
						else        
							t.(w[i]) := i;
						fi;
					fi;
				od;
				Hom := [];
				if x<0 then
					Hom[-x] := GrpWord([x],xx!.group);
					x := -x;
				fi;
				Hom := GrpWordHom(Hom,xx!.group);
				Hom2 := [];
				v := GrpWord(w2,xx!.group)^-1;
				Hom2[x] := GrpWord(w1,xx!.group)^-1 * GrpWord(Concatenation([x],w1),G) *v;
				Hom := GrpWordHom(Hom2)*Hom;
				w2 := v!.word;
				N := case3(x,Concatenation(w1,w2,w3),xx!.group);
				return [N[1],N[2]*Hom];
			fi; #End Nonoriented Case	
			Print("Not implemented yet\n");
			return [];
		end;
		if IsSquareGrpWord(x) then
			return NormalForm2(x);
		else
			TryNextMethod();
		fi;
	end
);

InstallMethod(GrpWordNormalFormInverseHom, "for a Grpword",
	[IsGrpWord],
	function(x)
		local NormalForm2;
		NormalForm2:= function(xx)
			local case10,case11a,case11b,case3,toInvert,vfind,i,j,t,x,vlen,v,w,v1,v2,w1,w2,w11,w12,w21,w22,w3,first,Hom,Hom2,y,N;
			Print("Call of NormalForm2¸with");
			View(xx!.word);
			Print("\n");
			xx:= GrpWordReducedForm(xx);
			w:= xx!.word;
			#Functions for Oriented GrpWords:
			# w = w1·x⁻·v·x·w2
			case10 := function(w1,v,w2,x,G)
				local N,Hom,h,c;
				#Print("Case 10:");
				#View([w1,v,w2,x]);
				#Print("\n");
				N := NormalForm2(GrpWord(Concatenation(w1,w2),G));
				h := N[1]!.word;
				Hom := [];
				Hom[x] := GrpWord(Concatenation([x],w2),G); #DONE
				if Length(h)=0 then
					return [GrpWord([-x,v,x],G),GrpWordHom(Hom)];
				fi;
				#Does N end with a constant?
				if IsInt(h[Length(h)]) then
					return [N[1]*GrpWord([-x,v,x],G),GrpWordHom(Hom)*N[2]]; #DONE
				else
					c:= h[Length(h)];
					Hom := [];
					Hom[x] := GrpWord(Concatenation([x],w2,[c^-1]),G); #DONE
					return [N[1][[1..Length(h)-1]]*GrpWord([-x,v,x,c],G),GrpWordHom(Hom)*N[2]]; #DONE
				fi;
			end;
			# w = w11·v⁻·w12·x⁻·v·x·w2
			case11a := function(w11,w12,v,w2,x,G)
				local N,Hom,h;
				#Print("Case 11a:");
				#View([w11,w12,v,w2,x]);
				#Print("\n");
				N := NormalForm2(GrpWord(Concatenation(w11,w12,w2),G));
				Hom := [];
				h := GrpWord(w11,G)^-1;
				Hom[x] := GrpWord(Concatenation(w11,[x]),G)*GrpWord(w12,G)^-1 * h ; #DONE
				Hom[v] := GrpWord(Concatenation(w11,[v]),G) *h; #DONE
				return [GrpWord([-v,-x,v,x],G)*N[1],GrpWordHom(Hom)*N[2]]; #DONE
			end;
			# w = w1·x⁻·v·x·w21·v⁻·w22
			case11b := function(w1,v,w21,w22,x,G)
				local N,Hom,h;
				#Print("Case 11b:");
				#View([w1,v,w21,w22,x]);
				#Print("\n");
				N := NormalForm2(GrpWord(Concatenation(w1,w21,w22),G));
				Hom := [];
				Hom[x] := GrpWord(Concatenation(w1,w21,[x]),G) *GrpWord(w1,G)^-1;#DONE
				Hom[v] := GrpWord(Concatenation(w1,w21,[-v]),G) *GrpWord(Concatenation(w1,w21),G)^-1;#DONE
				return [GrpWord([-x,-v,x,v],G)*N[1],GrpWordHom(Hom)*N[2]];#DONE
			end;
			# w = x²·w2
			case3 := function(x,w2,G)
				local N,N2,Hom,y,z;
				#Print("Case 3:");
				#View([x,w2]);
				#Print("\n");
				N := NormalForm2(GrpWord(w2,G));
				#Check if N start with [y,z]
				if Length(N[1]!.word)<4 or not IsInt(N[1]!.word[2]) or N[1]!.word[1]=N[1]!.word[2] then
					#Print("End is Ok.. leaving Case 3\n");
					return [GrpWord([x,x],G)*N[1],N[2]];
				else
					#Print("w2 contains commutator...\n");
					y := N[1]!.word[3];
					z := N[1]!.word[4];
					Hom := [];
					Hom[x] := GrpWord([x,x,-y,-x],G);#DONE
					Hom[y] := GrpWord([x,y,-x,-z,-x],G);#DONE
					Hom[z] := GrpWord([x,z],G);#DONE
					N2 := case3(z,N[1]!.word{[5..Length(N[1]!.word)]},G);
					return [GrpWord([x,x,y,y],G)*N2[1],N[2]*N2[2]*GrpWordHom(Hom)];#DONE
				fi;
			end;
			if IsOrientedGrpWord(xx) then
				if Length(w)<3 then
					return [xx,GrpWordHom([],xx!.group)];
				fi;
				#Print("Oriented");
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
				#Print("Counting dict: ",t,"\n");
				x := 0;
				vlen := -Length(w);
			for i in RecNames(t) do
				if t.(i)>vlen then
					x := i;
					vlen := t.(i);
				fi;
			od;
			x := Int(x);
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
			#Decomposition done
			if Length(v)=1 then #Case 1
				v := v[1];
				if IsInt(v) then #Case 1.1
					if v<0 then
						Hom2 := [];
						Hom2[-v] := GrpWord([v],xx!.group);#DONE
						Hom := Hom*GrpWordHom(Hom2);#DONE
					fi;
					i := Position(w1,-v);
					if not i = fail then #Case 1.1.a
						w11 := w1{[1..i-1]};
						w12 := w1{[i+1..Length(w1)]};
						Display(N[2]!.rules[1]!.word);
						return [N[1],Hom*N[2]];#DONE
					else #Case 1.1.b
						i := Position(w2,-v);
						if i = fail then 
							Error("Strange Error");
						fi;
						w21 := w2{[1..i-1]};
						w22 := w2{[i+1..Length(w2)]};
						N:= case11b(w1,AbsInt(v),w21,w22,x,xx!.group);
						return [N[1],Hom*N[2]];#DONE
					fi;
				else #Case 1.0
					N := case10(w1,v,w2,x,xx!.group);
					return [N[1],Hom*N[2]];#DONE
				fi;
				else #Case 2
					#Print("Case2.");
					y := 0;
					for i in v do
					if IsInt(i) then
						y := i;
						if i<0 then
							break;
						fi;
					fi;
					od;
					i := Position(v,y);
					if y>0 then
						Hom2 := [];
						Hom2[y] := GrpWord([-y],xx!.group);
						Hom := Hom*GrpWordHom(Hom2);#DONE
						y := -y;
					fi;
					y := -y;
					v1 := v{[1..i-1]};
					v2 := v{[i+1..Length(v)]};
					i := Position(w1,y);
					if not i = fail then #Case 2.a
						#Print("a. ");
						w11 := w1{[1..i-1]};
						w12 := w1{[i+1..Length(w1)]};
						N := case11a(w11,Concatenation(v2,v1),x,Concatenation(w12,w2),y,xx!.group);
						Hom2 := [];
						Hom2[x] :=GrpWord(Concatenation(v2,[x]),xx!.group)*GrpWord(Concatenation([y],w12),xx!.group)^-1;#DONE
						return [N[1],Hom*GrpWordHom(Hom2)*N[2]];#DONE
					else #Case 2.b
						#Print("b. ");
						i := Position(w2,y);
						if i = fail then 
							Error("Strange Error");
						fi;
						w21 := w2{[1..i-1]};
						w22 := w2{[i+1..Length(w2)]};
						N := case11a(Concatenation(w1,w21),Concatenation(v2,v1),x,w22,y,xx!.group);
						Hom2 := [];
						Hom2[x] := GrpWord(Concatenation(v2,[x],w21),xx!.group); #DONE
						return [N[1],Hom*GrpWordHom(Hom2)*N[2]];#DONE
					fi;
				fi; #End Case 2
				else #so not oriented
					#Print("Nonoriented Case:\n");
					#find x s.t. w = w1·x·w2·x·w3
					t:= rec();
					for i in [1..Length(w)] do
						if IsInt(w[i]) then
						if IsBound(t.(w[i])) then
							x:= w[i];
							w1:= w{[1..t.(w[i])-1]};
							w2:= w{[t.(w[i])+1..i-1]};
						w3:= w{[i+1..Length(w)]};
						break;
						else        
							t.(w[i]) := i;
						fi;
					fi;
				od;
				Hom := [];
				if x<0 then
					Hom[-x] := GrpWord([x],xx!.group);
					x := -x;
				fi;
				Hom := GrpWordHom(Hom,xx!.group);
				Hom2 := [];
				Hom2[x] := GrpWord(Concatenation(w1,[x],w2),xx!.group) * GrpWord(w1,G)^-1;#DONE
				Hom := Hom*GrpWordHom(Hom2);#DONE
				w2 := GrpWord(w2,G)^-1;
				w2 := w2!.word;
				N := case3(x,Concatenation(w1,w2,w3),xx!.group);
				return [N[1],Hom*N[2]];#DONE
			fi; #End Nonoriented Case	
			Print("Not implemented yet\n");
			return [];
		end;
		if IsSquareGrpWord(x) then
			return NormalForm2(x);
		else
			TryNextMethod();
		fi;
	end
);
InstallMethod(GrpWordDecomposed, "for a Grpword",
	[IsGrpWord],
	function(w)
		local Perm,A,C,tau,i,Var,L,v;
		if not IsGrpWordDecomposableRep(w) then
			w := GrpWordDecomposable(w);
		fi;
		A := AlphabetOfFRSemigroup(w!.group);
		Perm := SymmetricGroup(A);
		C := [];
		Var := Set(List(UnknownsOfGrpWord(w),AbsInt));
		for tau in Cartesian(ListWithIdenticalEntries(Length(Var),Perm))  do
			L := [];
			v := One(w!.group);
			for i in w!.word do
				if IsInt(i) then
					i := FRGrpWordUnknown(i,tau[Position(Var,AbsInt(i))],w!.group);
				fi;
				v := v *i;
			od;
			Add(C,[GrpWordReducedForm(v),tau]);
		od;
		return [C,w!.hom];
	end
);
rule_pr := function(grpwh)
	local N,h,x,y;
	h:= grpwh!.rules;
	for x in [1..Length(h)] do
		if IsBound(h[x]) then
			Print("[");
			for y in h[x]!.word do
				if IsInt(y) then
					Print(y,",");
				else 
					Print("c,");
				fi;
			od;
			Print("],");
		else 
			Print(",");
		fi;
	od;
	Print("\n");
end;
testfunc := function()
	local elms,e,L,xn,x;
	elms := [[1,1],[-1,-1],[1,1,2,2],[2,1,1,2],[2,1,-2,1],[2,-1,-2,-1],[2,-1,2,-1],[-2,-1,-1,2,a],[-2,-1,-1,-2,a],[-1,3,-1,2,3,2],[3,2,1,-3,1,a,2],[-1,-4,3,4,a,-1,2,3,c,2],[1,-5,a,5,b,-1,-2,3,a,4,-3,b,-4,c,2]];
	L := [];
	for e in elms do
		x := GrpWord(e,G);
		xn := GrpWordNormalForm(x);
		if ImageOfGrpWordHom(xn[2],x) <> xn[1] then
			Add(L,e);
		fi;
	od;
	Print("Errors happened at L: ");
	Display(L);
	Print("\n");
	L := [];
	for e in elms do
		x := GrpWord(e,G);
		xn := GrpWordNormalFormInverseHom(x);
		if ImageOfGrpWordHom(xn[2],xn[1]) <> x then
			Add(L,e);
		fi;
	od;
	Print("Errors happened at L: ");
	Display(L);
	Print("\n");

end;
