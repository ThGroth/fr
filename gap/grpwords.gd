DeclareCategory("IsGrpWord", IsMultiplicativeElementWithOne);
DeclareCategoryCollections("IsGrpWord");
DeclareRepresentation("IsGrpWordRep",
											 IsComponentObjectRep  and IsAttributeStoringRep,
											 ["word","group"]);
DeclareOperation("GrpWord", [IsList, IsGroup]);

DeclareAttribute("UnknownsOfGrpWord", [IsGrpWord]);
DeclareAttribute("WordNormalForm", IsGrpWord);

DeclareProperty("IsSquareGrpWord", IsGrpWord);
DeclareProperty("IsOrientedGrpWord", IsSquareGrpWord);
