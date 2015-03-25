DeclareCategory("IsGrpWord", IsMultiplicativeElementWithInverse);

DeclareCategoryCollections("IsGrpWord");
DeclareRepresentation("IsGrpWordRep",
 IsComponentObjectRep  and IsAttributeStoringRep,
 ["word","group"]);
DeclareOperation("GrpWord", [IsList, IsGroup]);

DeclareAttribute("UnknownsOfGrpWord",IsGrpWord);
DeclareAttribute("GrpWordReducedForm",IsGrpWord);
DeclareAttribute("GrpWordCyclReducedForm",IsGrpWord);
DeclareAttribute("WordNormalForm", IsGrpWord);
DeclareAttribute("LengthOfGrpWord",IsGrpWord);


DeclareProperty("IsSquareGrpWord", IsGrpWord);
DeclareProperty("IsOrientedGrpWord", IsSquareGrpWord);

DeclareCategory("IsGrpWordHom",IsMultiplicativeElementWithOne);
DeclareRepresentation("IsGrpWordHomRep", 
 IsComponentObjectRep  and IsAttributeStoringRep,
 ["rules"]);
DeclareOperation("GrpWordHom",[IsList]);
DeclareOperation("ImageOfGrpWordHom",[IsGrpWordHom,IsGrpWord]);
