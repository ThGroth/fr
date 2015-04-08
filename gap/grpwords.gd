###########################################################################
####                                                                   ####
####                    Categories and Representations                 ####
####                                                                   ####
###########################################################################
DeclareCategory("IsGrpWord", IsMultiplicativeElementWithInverse);
DeclareCategory("IsGrpWordHom",IsMultiplicativeElementWithOne);
DeclareCategory("IsFRGrpWord",IsMultiplicativeElementWithOne);
InstallTrueMethod(IsGrpWord,IsFRGrpWord);

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
DeclareAttribute("GrpWordNormalFormInverseHom", IsGrpWord);
DeclareAttribute("GrpWordNormalForm", IsGrpWord);
DeclareAttribute("LengthOfGrpWord",IsGrpWord);

DeclareProperty("IsPermGrpWord",IsGrpWord);
DeclareProperty("IsSquareGrpWord", IsGrpWord);
DeclareProperty("IsOrientedGrpWord", IsSquareGrpWord);


###########################################################################
####                                                                   ####
####                          Operations                               ####
####                                                                   ####
###########################################################################

DeclareOperation("GrpWordDecomposable", [IsGrpWord]);

DeclareOperation("GrpWordAsElement",[IsGrpWord]);
DeclareOperation("GrpWordHomCompose",[IsGrpWordHom,IsList,IsGroup]);
DeclareOperation("GrpWordDecomposed",[IsGrpWord]);
DeclareOperation("ImageOfGrpWordHom",[IsGrpWordHom,IsGrpWord]);
DeclareOperation("GrpWordToStates", [IsGrpWord, IsPerm]);

DeclareOperation("GrpWordSolve",[IsGrpWord]);
