###########################################################################
####                                                                   ####
####                    Categories and Representations                 ####
####                                                                   ####
###########################################################################
DeclareCategory("IsGrpWord", IsMultiplicativeElementWithInverse);
DeclareCategory("IsGrpWordHom",IsMultiplicativeElementWithOne);
DeclareCategory("IsFRGrpWord",IsMultiplicativeElementWithOne);

DeclareCategoryCollections("IsGrpWord");

DeclareRepresentation("IsGrpWordRep",
 IsComponentObjectRep  and IsAttributeStoringRep,
 ["word","group"]
);
DeclareRepresentation("IsGrpWordDecomposableRep",
	IsGrpWordRep,["word","group","hom"]
);
DeclareRepresentation("IsGrpWordHomRep", 
 IsComponentObjectRep  and IsAttributeStoringRep,
 ["rules"]
);
DeclareRepresentation("IsFRGrpWordStateRep", 
 IsComponentObjectRep  and IsAttributeStoringRep,
 ["states","activity"]
);
DeclareRepresentation("IsGrpWordStateRep", 
 IsGrpWordDecomposableRep,
 ["word","states","activity","hom","group"]
);

###########################################################################
####                                                                   ####
####                         Constructors                              ####
####                                                                   ####
###########################################################################

DeclareOperation("GrpWord", [IsList, IsGroup]);
DeclareOperation("GrpWordHom",[IsList]);
DeclareOperation("FRGrpWord",[IsList,IsPerm,IsGroup]);
DeclareOperation("FRGrpWordUnknown",[IsInt,IsPerm,IsFRGroup]);


###########################################################################
####                                                                   ####
####                   Attributes and Properties                       ####
####                                                                   ####
###########################################################################

DeclareAttribute("UnknownsOfGrpWord",IsGrpWord);
DeclareAttribute("GrpWordReducedForm",IsGrpWord);
DeclareAttribute("GrpWordCyclReducedForm",IsGrpWord);
DeclareAttribute("GrpWordNormalForm", IsGrpWord);
DeclareAttribute("LengthOfGrpWord",IsGrpWord);

DeclareProperty("IsSquareGrpWord", IsGrpWord);
DeclareProperty("IsOrientedGrpWord", IsSquareGrpWord);


###########################################################################
####                                                                   ####
####                          Operations                               ####
####                                                                   ####
###########################################################################

DeclareOperation("GrpWordDecomposable", [IsGrpWord]);

DeclareOperation("GrpWordDecomposed",[IsGrpWord]);
DeclareOperation("ImageOfGrpWordHom",[IsGrpWordHom,IsGrpWord]);
DeclareOperation("GrpWordToStates", [IsGrpWord, IsPerm]);
