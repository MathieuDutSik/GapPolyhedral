POLYDEC_IsInSpaceRelativeInterior:=function(eCase, TheMat)
  local n, ImageBasis, ImageMat, ListCoef, result;
  n:=Length(TheMat);
  ImageBasis:=List(eCase.Basis, SymmetricMatrixToVector);
  ImageMat:=SymmetricMatrixToVector(TheMat);
  ListCoef:=SolutionMat(ImageBasis, ImageMat);
  result:=First(eCase.ListFacets, x->x*ListCoef <=0);
  if result=fail then
    return true;
  else
    return false;
  fi;
end;






POLYDEC_RandomPositiveElement:=function(eCase)
  local TheSum, eMat, TheSpread;
  TheSum:=0;
  TheSpread:=30;
  for eMat in eCase.Basis
  do
    TheSum:=TheSum+Random([-TheSpread..TheSpread])*eMat;
  od;
  while(true)
  do
    if POLYDEC_IsInSpaceRelativeInterior(eCase, TheSum)=true then
      if IsPositiveDefiniteSymmetricMatrix(TheSum)=false then
        Error("We have a big bug here");
      fi;
      break;
    else
      TheSum:=TheSum+eCase.SuperMat;
    fi;
  od;
  return TheSum;
end;


POLYDEC_RandomPositiveElementFixedSymmetry:=function(eCase)
  local TheMat, GRP;
  while(true)
  do
    TheMat:=POLYDEC_RandomPositiveElement(eCase);
    GRP:=ArithmeticAutomorphismGroup([TheMat]);
    if Order(GRP)=Order(eCase.SymmGrpPtWs) then
      return TheMat;
    fi;
  od;
end;







POLYDEC_RandomPrimitiveElement:=function(eCase, PathInitial, IsSaving)
  local nbTry, DelCO, TheGramMat, KillingDelaunay, KillingAdjacency, iter, MaximalMemorySave;
  nbTry:=0;
  KillingDelaunay:=function(EXT_Delaunay)
    local SetEqualities, eVect;
    SetEqualities:=Set(ListEqualitiesDelaunay(EXT_Delaunay, eCase.Basis));
    if Length(SetEqualities)>1 then
      Print("Kill with |EXT|=", Length(EXT_Delaunay), "\n");
      return rec(Reason:="kill by rank");
    fi;
    eVect:=SetEqualities[1];
    if eVect*eVect>0 then
      Print("Kill with a |EXT|=", Length(EXT_Delaunay), "\n");
      return rec(Reason:="kill by rank");
    else
      return false;
    fi;
  end;
  KillingAdjacency:=function(EXT1, EXT2)
    return false;
  end;
  MaximalMemorySave:=false;
  while(true)
  do
    TheGramMat:=POLYDEC_RandomPositiveElementFixedSymmetry(eCase);
    for iter in [1..12]
    do
      DelCO:=DelaunayDescriptionStandardKernel(TheGramMat, eCase.SymmGrpPtWs, PathInitial, IsSaving, KillingDelaunay, KillingAdjacency, MaximalMemorySave);
      if DelCO<>rec(Reason:="kill by rank") then
        return rec(GramMat:=TheGramMat, DelCO:=DelCO);
      fi;
      TheGramMat:=TheGramMat+eCase.SuperMat;
    od;
    nbTry:=nbTry+1;
    Print("failure at try Nr.", nbTry, "  retrying...\n");
  od;
end;





POLYDEC_IsItEntirelyContainedInCone:=function(eCase, EXT)
  local eEXT, result;
  for eEXT in EXT
  do
    result:=First(eCase.ListFacets, x->x*eEXT<0);
    if result<>fail then
      return false;
    fi;
  od;
  return true;
end;


POLYDEC_EnumerationProcedureLtypeCore:=function(eCase, LtypeDatabase, DataPolyhedralTiling, PrimitiveElementFct, KillingFace)
  local FuncInsert, IsFinished, FACINEQ, FACred, EXTred, eFac, TheSumFace, NewGramMatFace, i, ePos, FlippingInfo, TheFlip, iOrb, n, jOrb, test, RML, ListNormGen, DiscInfo, nbOrbit, testIso, TheLtype, nbTry, ListLtypes, DimSpace, TotalNbLtype, RecExtRay, eStrMax;
  #
  BasicCoherencyCheckups(eCase);
  TotalNbLtype:=0;
  n:=eCase.n;
  #
  RecExtRay:=TSPACE_GetExtremeRayFunctions(eCase);

  DimSpace:=Length(eCase.Basis);
  #
  ListLtypes:=[];
  FuncInsert:=function(OneLtype)
    local FAC1, FAC2, EXT2, eEXT, ListRank, GramMat, i, kOrb, testIso, eInv, ListSizeDelaunay, eDelaunay, ListStatusFace, eFac, TheSum, TheAutGroup, TheRecord, nbType, testIntersection, MyDiscInfo, testtotalinclusion, extRaySig, testEquiv, eDiscInfo, TheStabER, OrbSize, EXTrepMatrix, TheStabMatr, eMat;
    FAC1:=WriteFaceInequalities(OneLtype, eCase);
    EXT2:=DualDescription(FAC1.ListInequalities);
    FAC2:=EliminationByRedundancyCone(FAC1.ListInequalities, EXT2);
    ListRank:=List(EXT2, x->RankMat(FuncComputeMat(eCase.Basis, x)));
    ListSizeDelaunay:=List(OneLtype, x->[Length(x.EXT), Order(x.TheStab.PermutationStabilizer)]);
    ListStatusFace:=[];
    for eFac in FAC2
    do
      Add(ListStatusFace, RankMat(FuncComputeMat(eCase.Basis, Sum(Filtered(EXT2, x->eFac*x=0)))));
    od;
    testtotalinclusion:=POLYDEC_IsItEntirelyContainedInCone(eCase, EXT2);
    eInv:=rec(BasicInv:=[Length(FAC1.ListInequalities), Length(FAC2), Length(EXT2)], RankExtremeRay:=Collected(ListRank), DelaunayRepartition:=Collected(ListSizeDelaunay), StatusFaces:=Collected(ListStatusFace), totalinclusion:=testtotalinclusion);
    testIntersection:=POLYDEC_HasConeNonVoidIntersection(eCase, FAC2);
    if testIntersection=false then
      return false;
    fi;
    GramMat:=Sum(List(EXT2, u->RemoveFractionMatrix(FuncComputeMat(eCase.Basis, u))));
    extRaySig:=RecExtRay.GetExtRaySignature(GramMat);
    for kOrb in [1..LtypeDatabase.FuncGetNumberLtype()]
    do
      if LtypeDatabase.FuncGetInv(kOrb)=eInv then
        eDiscInfo:=LtypeDatabase.FuncGetDiscInfo(kOrb);
        testEquiv:=RepresentativeAction(RecExtRay.PermGrpExtRays, extRaySig, eDiscInfo.extRaySig, Permuted);
        if testEquiv<>fail then
          return true;
        fi;
      fi;
    od;
    MyDiscInfo:=rec(extRaySig:=extRaySig, GramMat:=GramMat);
    TheStabER:=Stabilizer(RecExtRay.PermGrpExtRays, extRaySig, Permuted);
    LtypeDatabase.FuncInsertLtype(OneLtype, MyDiscInfo, eInv);
    OrbSize:=Order(RecExtRay.PermGrpExtRays)/Order(TheStabER);
    EXTrepMatrix:=[];
    for eEXT in EXT2
    do
      eMat:=NullMat(n, n);
      for i in [1..DimSpace]
      do
        eMat:=eMat+eEXT[i]*eCase.Basis[i];
      od;
      Add(EXTrepMatrix, RemoveFractionMatrix(eMat));
    od;
    TheStabMatr:=PreImage(RecExtRay.phiExtRay, TheStabER);
    TheRecord:=rec(
        FAC:=FAC2, EXT:=EXT2, EXTrepMatrix:=EXTrepMatrix, OrbSize:=OrbSize, totalinclusion:=testtotalinclusion, TheStabER:=TheStabER, TheStabMatr:=TheStabMatr, Ltype:=OneLtype);
    TotalNbLtype:=TotalNbLtype+OrbSize;
    Add(ListLtypes, TheRecord);
    nbType:=LtypeDatabase.FuncGetNumberLtype();
    Print("Find a new Ltype, now we have ", nbType, " Ltypes\n");
    return true;
  end;
  #
  if LtypeDatabase.FuncGetNumberLtype()=0 then
    nbTry:=0;
    while(true)
    do
      RML:=PrimitiveElementFct();
      test:=FuncInsert(RML.DelCO);
      nbTry:=nbTry+1;
      if test=true then
        break;
      fi;
      Print("Actually it should work\n");
      Print("It is trully a bug that it did not find a domain intersecting the Minkovski domain\n");
      Error("Please correct");
    od;
    Print("We needed ", nbTry, " tries\n");
  fi;
  #
  while(true)
  do
    IsFinished:=true;
    nbOrbit:=LtypeDatabase.FuncGetNumberLtype();
    Print("nbOrbit=", nbOrbit, "\n");
    for iOrb in [1..nbOrbit]
    do
      if LtypeDatabase.FuncGetStatus(iOrb)="NO" then
        ListNormGen:=[];
        Print("Beginning treatment of orbit ", iOrb, "\n");
        IsFinished:=false;
        #
        TheLtype:=LtypeDatabase.FuncGetLtype(iOrb);
        DiscInfo:=LtypeDatabase.FuncGetDiscInfo(iOrb);
        FACINEQ:=WriteFaceInequalities(TheLtype, eCase);
        EXTred:=DualDescription(FACINEQ.ListInequalities);
        FACred:=EliminationByRedundancyCone(FACINEQ.ListInequalities, EXTred);
        for eFac in FACred
        do
          TheSumFace:=Sum(Filtered(EXTred, x->x*eFac=0));
          NewGramMatFace:=FuncComputeMat(eCase.Basis, TheSumFace);
          if RankMat(NewGramMatFace)=n then
            # we are not sure that this check is really that necessary
            if KillingFace(eFac)=false then
              ePos:=Position(FACINEQ.ListInequalities, eFac);
              FlippingInfo:=FACINEQ.ListInformations[ePos];
              TheFlip:=FlippingLtype(TheLtype, DiscInfo.GramMat, FlippingInfo, DataPolyhedralTiling);
              test:=FuncInsert(TheFlip);
              if IsBound(eCase.MaximumNbType) then
                if Length(ListLtypes) > eCase.MaximumNbType then
                  eStrMax:=Concatenation("> ", String(TotalNbLtype));
                  return rec(ListLtypes:=ListLtypes, TotalNbLtype:=eStrMax);
                fi;
              fi;
            fi;
          fi;
        od;
        ListNormGen:="We do not care";
        LtypeDatabase.FuncLtypeInsertGenerators(ListNormGen, iOrb);
      fi;
    od;
    if IsFinished=true then
      break;
    fi;
  od;
  #
  return rec(ListLtypes:=ListLtypes, TotalNbLtype:=TotalNbLtype);
end;

POLYDEC_GetSymmetricGramMat:=function(eCase)
  local dimspace, ListGramMat, eRay, TheGramMat, i, ListPermGens, eGen, eList, GRPray, O, ListSumsO, eO, iRay, eGramMat;
  dimspace:=Length(eCase.Basis);
  ListGramMat:=[];
  for eRay in eCase.ListExtRays
  do
    TheGramMat:=NullMat(eCase.n, eCase.n);
    for i in [1..dimspace]
    do
      TheGramMat:=TheGramMat+eRay[i]*eCase.Basis[i];
    od;
    Add(ListGramMat, RemoveFractionMatrix(TheGramMat));
  od;
  ListPermGens:=[];
  for eGen in GeneratorsOfGroup(eCase.SymmGrpGlob)
  do
    eList:=List(ListGramMat, x->Position(ListGramMat, eGen*x*TransposedMat(eGen)));
    Add(ListPermGens, PermList(eList));
  od;
  GRPray:=Group(ListPermGens);
  O:=Orbits(GRPray, [1..Length(eCase.ListExtRays)], OnPoints);
  ListSumsO:=[];
  for eO in O
  do
    TheGramMat:=NullMat(eCase.n, eCase.n);
    for iRay in eO
    do
      TheGramMat:=TheGramMat+ListGramMat[iRay];
    od;
    Add(ListSumsO, RemoveFractionMatrix(TheGramMat));
  od;
  TheGramMat:=NullMat(eCase.n, eCase.n);
  for eGramMat in ListSumsO
  do
    TheGramMat:=TheGramMat+eGramMat;
  od;
  return TheGramMat;
end;


POLYDEC_IsReducedToOneLtype_VersionOpt:=function(eCase)
  local ThePath, PathLtype, IsSaving, PrimitiveElementFct, FileFacets, PathSave, dimspace, FACred, RML, FAC1, EXT2, FAC2, PathInitial, nbTry, DelCO, TheGramMat, KillingDelaunay, KillingAdjacency, iter, MaximalMemorySave, TheReply, FCT, InvariantBasis, DelCOsmall, PointGRP, i, eRay, GRPray, ListSumsO, iRay, O, eO, ListGramMat, ListPermGens, eList, eGen, eGramMat, DoAdditionalTest;
  ThePath:=Filename(POLYHEDRAL_tmpdir,"");
  dimspace:=Length(eCase.Basis);
  PathSave:=Concatenation(ThePath, "/POLYDEC/");
  Exec("mkdir -p ", PathSave);
  PathInitial:=Concatenation(PathSave, "InitialLtype/");
  Exec("mkdir -p ", PathInitial);
  IsSaving:=false;
  nbTry:=0;
  KillingDelaunay:=function(EXT_Delaunay)
    local SetEqualities, eVect;
    SetEqualities:=Set(ListEqualitiesDelaunay(EXT_Delaunay, eCase.Basis));
    if Length(SetEqualities)>1 then
      Print("Kill with |EXT|=", Length(EXT_Delaunay), "\n");
      return rec(Reason:="kill by rank");
    fi;
    eVect:=SetEqualities[1];
    if eVect*eVect>0 then
      Print("Kill with a |EXT|=", Length(EXT_Delaunay), "\n");
      return rec(Reason:="kill by rank");
    else
      return false;
    fi;
  end;
  KillingAdjacency:=function(EXT1, EXT2)
    local ExtractedBasis, eVert, RedIneq, ListVect, ListPositive, ListStrictlyPositive, nbFacet, iFace, eReply, iFac, TheConstraint, ListSetStrictPositive;
    ExtractedBasis:=RowReduction(EXT1, Length(EXT1[1])).EXT;
    eVert:=Difference(Set(EXT2), Set(EXT1))[1];
    RedIneq:=VoronoiLinearInequality(ExtractedBasis, eVert, eCase.Basis);
    ListVect:=[];
    ListPositive:=[];
    nbFacet:=Length(eCase.ListFacets);
    for iFac in [1..nbFacet]
    do
      Add(ListPositive, iFac);
      Add(ListVect, eCase.ListFacets[iFac]);
    od;
    Add(ListVect, -RedIneq{[2..dimspace+1]});
    ListStrictlyPositive:=[nbFacet+1];
    ListSetStrictPositive:=[];
    TheConstraint:=rec(ListSetStrictPositive:=ListSetStrictPositive, 
                       ListStrictlyPositive:=ListStrictlyPositive,
                       ListPositive:=ListPositive);
    eReply:=SearchPositiveRelation(ListVect, TheConstraint);
    if eReply=false then
      return rec(Reason:="kill by inequalities");
    fi;
    return false;
  end;
  TheGramMat:=POLYDEC_GetSymmetricGramMat(eCase);
  InvariantBasis:=__ExtractInvariantZBasisShortVectorNoGroup(TheGramMat);
#  Print("|InvariantBasis|=", Length(InvariantBasis), "\n");
  PointGRP:=ArithmeticAutomorphismMatrixFamily_HackSouvignier_V2("", [TheGramMat], InvariantBasis);
#  Print("|PointGRP|=", Order(PointGRP), "\n");
  for eGen in GeneratorsOfGroup(PointGRP)
  do
    eList:=List(ListGramMat, x->Position(ListGramMat, eGen*x*TransposedMat(eGen)));
    if PermList(eList)=fail then
      Print("The group PointGRP does not preserve the extreme rays\n");
      Print("This is not allowed and not supposed to happen\n");
      Error("Please debug from that point");
    fi;
  od;
  MaximalMemorySave:=false;
  TheReply:=DelaunayDescriptionStandardKernel(TheGramMat, PointGRP, PathInitial, IsSaving, KillingDelaunay, KillingAdjacency, MaximalMemorySave);
  if TheReply=rec(Reason:="kill by rank") then
    # if the rank is not correct, then this means that
    # the 
    return false;
  fi;
  if TheReply=rec(Reason:="kill by inequalities") then
    # if some inequality is not respected, then it has to be wrong.
    return false;
  fi;
  # There is actually no need for additional tests at this
  # point (but the global symmetry group should have preserved
  # the cone spanned by the extreme rays)
  DoAdditionalTest:=false;
  if DoAdditionalTest=true then
    Print("Before Symmetry breaking\n");
    DelCOsmall:=SymmetryBreakingDelaunayDecomposition(TheReply, PointGRP, eCase.SymmGrpPtWs, InvariantBasis);
    Print("After Symmetry breaking\n");
    FAC1:=WriteFaceInequalities(DelCOsmall, eCase);
    EXT2:=DualDescription(FAC1.ListInequalities);
    FAC2:=EliminationByRedundancyCone(FAC1.ListInequalities, EXT2);
    FACred:=List(FAC2, x->RemoveFraction(x{[2..dimspace+1]}));
    TheReply:=Set(FACred)=Set(eCase.ListFacets);
    if TheReply=false then
      Error("We decidedly cannot bypass the symmetry breaking");
    fi;
  fi;
  return true;
end;




POLYDEC_IsReducedToOneLtype:=function(eCase)
  local ThePath, PathLtype, IsSaving, PrimitiveElementFct, FileFacets, PathSave, dimspace, FACred, RML, FAC1, EXT2, FAC2, PathInitial, nbTry, DelCO, TheGramMat, KillingDelaunay, KillingAdjacency, iter, MaximalMemorySave, TheReply, FCT;
  ThePath:=Filename(POLYHEDRAL_tmpdir,"");
  dimspace:=Length(eCase.Basis);
  PathSave:=Concatenation(ThePath, "/POLYDEC/");
  Exec("mkdir -p ", PathSave);
  PathInitial:=Concatenation(PathSave, "InitialLtype/");
  Exec("mkdir -p ", PathInitial);
  IsSaving:=false;
  nbTry:=0;
  KillingDelaunay:=function(EXT_Delaunay)
    local SetEqualities, eVect;
    SetEqualities:=Set(ListEqualitiesDelaunay(EXT_Delaunay, eCase.Basis));
    if Length(SetEqualities)>1 then
      Print("Kill with |EXT|=", Length(EXT_Delaunay), "\n");
      return rec(Reason:="kill by rank");
    fi;
    eVect:=SetEqualities[1];
    if eVect*eVect>0 then
      Print("Kill with a |EXT|=", Length(EXT_Delaunay), "\n");
      return rec(Reason:="kill by rank");
    else
      return false;
    fi;
  end;
  KillingAdjacency:=function(EXT1, EXT2)
    local ExtractedBasis, eVert, RedIneq, ListVect, ListPositive, ListStrictlyPositive, nbFacet, iFace, eReply, iFac, TheConstraint, ListSetStrictPositive;
    ExtractedBasis:=RowReduction(EXT1, Length(EXT1[1])).EXT;
    eVert:=Difference(Set(EXT2), Set(EXT1))[1];
    RedIneq:=VoronoiLinearInequality(ExtractedBasis, eVert, eCase.Basis);
    ListVect:=[];
    ListPositive:=[];
    nbFacet:=Length(eCase.ListFacets);
    for iFac in [1..nbFacet]
    do
      Add(ListPositive, iFac);
      Add(ListVect, eCase.ListFacets[iFac]);
    od;
    Add(ListVect, -RedIneq{[2..dimspace+1]});
    ListStrictlyPositive:=[nbFacet+1];
    ListSetStrictPositive:=[];
    TheConstraint:=rec(ListSetStrictPositive:=ListSetStrictPositive, 
                       ListStrictlyPositive:=ListStrictlyPositive,
                       ListPositive:=ListPositive);
    eReply:=SearchPositiveRelation(ListVect, TheConstraint);
    if eReply=false then
      return rec(Reason:="kill by inequalities");
    fi;
    return false;
  end;
  MaximalMemorySave:=false;
  FCT:=function()
    while(true)
    do
      TheGramMat:=POLYDEC_RandomPositiveElementFixedSymmetry(eCase);
      for iter in [1..12]
      do
        TheReply:=DelaunayDescriptionStandardKernel(TheGramMat, eCase.SymmGrpPtWs, PathInitial, IsSaving, KillingDelaunay, KillingAdjacency, MaximalMemorySave);
        if TheReply<>rec(Reason:="kill by inequalities") and TheReply<>rec(Reason:="kill by rank") then
          return rec(success:=1, GramMat:=TheGramMat, DelCO:=TheReply);
        fi;
        if TheReply=rec(Reason:="kill by inequalities") then
          return rec(success:=0);
        fi;
        TheGramMat:=TheGramMat+eCase.SuperMat;
      od;
      nbTry:=nbTry+1;
      Print("failure at try Nr.", nbTry, "  retrying...\n");
    od;
  end;
  RML:=FCT();
  if RML.success=0 then
    Print("Leaving here at lin prog test\n");
    return false;
  fi;
  FAC1:=WriteFaceInequalities(RML.DelCO, eCase);
  EXT2:=DualDescription(FAC1.ListInequalities);
  FAC2:=EliminationByRedundancyCone(FAC1.ListInequalities, EXT2);
  FACred:=List(FAC2, x->RemoveFraction(x{[2..dimspace+1]}));
#  Print("|FACred|=", Length(FACred), " |ListFacets|=", Length(eCase.ListFacets), "\n");
  return Set(FACred)=Set(eCase.ListFacets);
end;





#
# eCase:=rec(
#    n:= the dimension, 
#    Basis:=  basis of matrices spanning the cone
#    [Optional] MaximumNbType:= the maximum number of types. If above return corresponding error.
#    ListExtRays:= list of extreme rays
#    ListFacets:= list of facet defining inequalities
#    SymmGrpGlob:= the matrix group preserving the considered polyhedral
#                  cone globally (necessarily finite, please fix the
#                  size in advance)
#    GlobInvarMat:= a matrix globally invariant by the group SymmGrpGlob
#                   (there is necessarily one since the group is finite)
#    SymmGrpPtWs:= the matrix group preserving every element of 
#                  the cone  
#    SuperMat:= positive definite matrix, belonging to the relative
#               interior of the cone)
POLYDEC_EnumerationLtype:=function(eCase)
  local ThePath, PathLtype, IsSaving, MemorySave, LtypeDatabase, PrimitiveElementFct, RepartPath, DataPolyhedralTiling, KillingFace, FileFacets, ListPos, ListInequalities, PathSave, TheSoughtInfo;
  ThePath:=Filename(POLYHEDRAL_tmpdir,"");
  PathSave:=Concatenation(ThePath, "/POLYDEC/");
  Exec("mkdir -p ", PathSave);
  PathLtype:=Concatenation(PathSave, "Ltypes/");
  Exec("mkdir -p ", PathLtype);
  IsSaving:=true;
  MemorySave:=false;
  LtypeDatabase:=LtypeDatabaseManagement(PathLtype, IsSaving, MemorySave);
  PrimitiveElementFct:=function()
    local PathInitial;
    PathInitial:=Concatenation(PathSave, "InitialLtype/");
    Exec("mkdir -p ", PathInitial);
    return POLYDEC_RandomPrimitiveElement(eCase, PathInitial, false);
  end;
  RepartPath:=Concatenation(PathSave, "Repartitionning/");
  Exec("mkdir -p ", RepartPath);
  DataPolyhedralTiling:=rec(PathSAVE:=RepartPath, Saving:=IsSaving,
                            DualDescriptionFunction:=poly_private@DualDescriptionLRS_Reduction);
  KillingFace:=function(eFac)
    return false;
  end;
  TheSoughtInfo:=POLYDEC_EnumerationProcedureLtypeCore(eCase, LtypeDatabase, DataPolyhedralTiling, PrimitiveElementFct, KillingFace);
  return TheSoughtInfo;
end;


ApplicationPOLYDEC_FreeStructure:=function(eRecFree)
  local n, GetScalProdSignature, GetECase,  GetLtypeDecomposition, Single_KillingFunction;
  n:=Length(eRecFree.GramMat);
  GetScalProdSignature:=function(TheGram, ListVect)
    local ListDiag, ListOffDiag, nbVect, iVect, jVect, eScal;
    ListDiag:=List(ListVect, x->x*TheGram*x);
    ListOffDiag:=[];
    nbVect:=Length(ListVect);
    for iVect in [1..nbVect-1]
    do
      for jVect in [iVect+1..nbVect]
      do
        eScal:=ListVect[iVect]*TheGram*ListVect[jVect];
        Add(ListOffDiag, eScal);
      od;
    od;
    return rec(ListDiag:=Collected(ListDiag), ListOffDiag:=Collected(ListOffDiag));
  end;
  GetECase:=function(ListIndices)
    local ListMatrix, iIdx, vVect, eNewMat, ListVect, eRedInfo, ListVectRed, ListRays, FAC, TheStabGlobPerm, MatrGrpGlob, TheStabPtWsPerm, MatrGrpPtWs, SuperMat, eCase, eMat, TheSignature;
    ListMatrix:=[eRecFree.GramMat];
    for iIdx in ListIndices
    do
      vVect:=eRecFree.ListFreeVect[iIdx]*eRecFree.GramMat;
      eNewMat:=TransposedMat([vVect])*[vVect];
      Add(ListMatrix, eNewMat);
    od;
    TheSignature:=GetScalProdSignature(eRecFree.GramMat, eRecFree.ListFreeVect{ListIndices});
    ListVect:=List(ListMatrix, SymmetricMatrixToVector);
    eRedInfo:=RowReduction(ListVect);
    ListVectRed:=eRedInfo.EXT;
    ListRays:=List(ListVect, x->SolutionMat(ListVectRed, x));
    FAC:=DualDescription(ListRays);
    TheStabGlobPerm:=Stabilizer(eRecFree.PermGRPfree, ListIndices, OnSets);
    MatrGrpGlob:=PreImage(eRecFree.phi, TheStabGlobPerm);
    TheStabPtWsPerm:=Stabilizer(eRecFree.PermGRPfree, ListIndices, OnTuples);
    MatrGrpPtWs:=PreImage(eRecFree.phi, TheStabPtWsPerm);
    SuperMat:=NullMat(n,n);
    for eMat in ListMatrix
    do
      SuperMat:=SuperMat+eMat;
    od;
    return rec(n:=n, 
               Basis:=ListMatrix{eRedInfo.Select}, 
               ListExtRays:=ListRays, 
               ListFacets:=FAC, 
               SuperMat:=SuperMat, 
               GlobInvarMat:=eRecFree.GramMat, 
               SymmGrpGlob:=MatrGrpGlob, 
               SymmGrpPtWs:=MatrGrpPtWs);
  end;
  GetLtypeDecomposition:=function(ListIndices)
    local eCase;
    eCase:=GetECase(ListIndices);
    return POLYDEC_EnumerationLtype(eCase);
  end;
  Single_KillingFunction:=function(ListIndices)
    local eCase, test1, test1b;
    if IsUnimodularVectorSystem(eRecFree.ListFreeVect{ListIndices})=false then
      return true;
    fi;
    eCase:=GetECase(ListIndices);
#    test1b:=POLYDEC_IsReducedToOneLtype(eCase);
    test1:=POLYDEC_IsReducedToOneLtype_VersionOpt(eCase);
    if test1=true then
      return false;
    fi;
    return true;
  end;
  return rec(Single_KillingFunction:=Single_KillingFunction, 
             GetLtypeDecomposition:=GetLtypeDecomposition, 
             GetECase:=GetECase);
end;
