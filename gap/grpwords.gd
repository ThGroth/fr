DeclareCategory("IsGrpWord", IsMultiplicativeElementWithOne);
DeclareCategoryCollections("IsGrpWord");
DeclareRepresentation("IsGrpWordRep",
											 IsComponentObjectRep  and IsAttributeStoringRep,
											 ["word","group"]);
DeclareOperation("GrpWord", [IsList, IsGroup]);
