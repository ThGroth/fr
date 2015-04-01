DeclareCategory("IsGrpWord", IsMultiplicativeElementWithInverse);

DeclareCategoryCollections("IsGrpWord");
DeclareRepresentation("IsGrpWordRep",
 IsComponentObjectRep  and IsAttributeStoringRep,
 ["word","group"]);
DeclareRepresentation("IsGrpWordDecomposableRep",
	IsGrpWordRep,["word","group","hom"]);

DeclareOperation("GrpWord", [IsList, IsGroup]);
DeclareOperation("GrpWordDecomposable", [IsGrpWord]);

DeclareAttribute("UnknownsOfGrpWord",IsGrpWord);
DeclareAttribute("GrpWordReducedForm",IsGrpWord);
DeclareAttribute("GrpWordCyclReducedForm",IsGrpWord);
DeclareAttribute("GrpWordNormalForm", IsGrpWord);
DeclareAttribute("LengthOfGrpWord",IsGrpWord);

DeclareOperation("GrpWordDecomposed",[IsGrpWord]);

DeclareProperty("IsSquareGrpWord", IsGrpWord);
DeclareProperty("IsOrientedGrpWord", IsSquareGrpWord);

DeclareCategory("IsGrpWordHom",IsMultiplicativeElementWithOne);
DeclareRepresentation("IsGrpWordHomRep", 
 IsComponentObjectRep  and IsAttributeStoringRep,
 ["rules"]);
DeclareOperation("GrpWordHom",[IsList]);
DeclareOperation("ImageOfGrpWordHom",[IsGrpWordHom,IsGrpWord]);

DeclareCategory("IsFRGrpWordLetter", IsMultiplicativeElementWithInverse);
DeclareRepresentation("IsGrpWordLetterStateRep", 
 IsComponentObjectRep  and IsAttributeStoringRep,
 ["states","activity"]);
DeclareOperation("FRGrpWordLetter", [IsInt, IsPerm,IsFRGroup]);
