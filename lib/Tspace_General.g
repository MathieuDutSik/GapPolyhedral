FuncComputeMat:=function(TheBasis, eVect)
  local DimSpace, n, GramMat, i;
  DimSpace:=Length(TheBasis);
  if Length(eVect)<>DimSpace then
    Error("Dimension error in FuncComputeMat");
  fi;
  n:=Length(TheBasis[1]);
  GramMat:=NullMat(n, n);
  for i in [1..DimSpace]
  do
    GramMat:=GramMat+eVect[i]*TheBasis[i];
  od;
  return GramMat;
end;


# See for definition of this function
# https://en.wikipedia.org/wiki/Crystallographic_restriction_theorem
# A value m is realizable as an order if and only if psi(m) <= N
PsiFunction:=function(m)
  local LFact, LColl, FuncVal, eColl, p, eMult, partVal;
  LFact:=FactorsInt(m);
  LColl:=Collected(LFact);
  FuncVal:=0;
  for eColl in LColl
  do
    p:=eColl[1];
    eMult:=eColl[2];
    if p=2 then
      if eMult=1 then
        partVal:=0;
      else
        partVal:=2^(eMult-1);
      fi;
    else
      partVal:=p^(eMult-1) * (p-1);
    fi;
    FuncVal:=FuncVal + partVal;
  od;
  return FuncVal;
end;


SerreClassOfFixedDimension:=function(N)
  local ListVal, ListValPrime, eVal, psiVal;
  ListVal:=[];
  ListValPrime:=[];
  # Very stupid, but what can we do
  for eVal in [2..10000]
  do
    psiVal:=PsiFunction(eVal);
    if psiVal <= N then
      Add(ListVal, eVal);
      if IsPrime(eVal) then
        Add(ListValPrime, eVal);
      fi;
    fi;
  od;
  return rec(ListVal:=ListVal, ListValPrime:=ListValPrime);
end;





BasisExpansion:=function(TheBasis, TheMat)
  local ListVector;
  ListVector:=List(TheBasis, SymmetricMatrixToVector);
  return Concatenation([0], SolutionMat(ListVector, SymmetricMatrixToVector(TheMat)));
end;



GetScalProdMatrix:=function(TheBasis, SuperMat)
  local DimSpace, ScalProdMatrix, InvSuper, i, j, eScal;
  DimSpace:=Length(TheBasis);
  ScalProdMatrix:=NullMat(DimSpace, DimSpace);
  InvSuper:=Inverse(SuperMat);
  for i in [1..DimSpace]
  do
    for j in [1..DimSpace]
    do
      eScal:=Trace(TheBasis[i]*InvSuper*TheBasis[j]*InvSuper);
      ScalProdMatrix[i][j]:=eScal;
    od;
  od;
  return ScalProdMatrix;
end;

IsTspaceBasisIntegral:=function(TheBasis)
  local n, ListVect, eMat, eVect, i, j, TotalRnk, TotalBasis, NSP, ListSol, eRedMat, TheIndex;
  n:=Length(TheBasis[1]);
  ListVect:=[];
  for eMat in TheBasis
  do
    eVect:=[];
    for i in [1..n]
    do
      Add(eVect, eMat[i][i]);
    od;
    for i in [1..n-1]
    do
      for j in [i+1..n]
      do
        Add(eVect, 2*eMat[i][j]);
      od;
    od;
    Add(ListVect, eVect);
  od;
  if IsIntegralMat(ListVect)=false then
    return false;
  fi;
  TotalRnk:=n*(n+1)/2;
  if RankMat(ListVect)=TotalRnk then
    TotalBasis:=IdentityMat(TotalRnk);
  else
    NSP:=NullspaceIntMat(TransposedMat(ListVect));
    TotalBasis:=NullspaceIntMat(TransposedMat(NSP));
  fi;
  ListSol:=List(ListVect, x->SolutionMat(TotalBasis, x));
  eRedMat:=BaseIntMat(ListSol);
  TheIndex:=AbsInt(DeterminantMat(eRedMat));
  return TheIndex=1;
end;


GetIntegralValuedBasis:=function(Basis)
  local n, DimSpace, ListVect, i, j, eVect, ListVectBas, NewBasis, iLine, jLine, eSol, NewMat;
  n:=Length(Basis[1]);
  DimSpace:=Length(Basis);
  ListVect:=[];
  for i in [1..n]
  do
    eVect:=List(Basis, x->x[i][i]);
    Add(ListVect, eVect);
  od;
  for i in [1..n-1]
  do
    for j in [i+1..n]
    do
      eVect:=List(Basis, x->2*x[i][j]);
      Add(ListVect, eVect);
    od;
  od;
  ListVectBas:=GetZbasis(ListVect);
  if Length(ListVectBas)<>Length(Basis) then
    Error("Mental error");
  fi;
  NewBasis:=[];
  for iLine in [1..DimSpace]
  do
    eVect:=ListWithIdenticalEntries(DimSpace, 0);
    eVect[iLine]:=1;
    eSol:=SolutionMat(TransposedMat(ListVectBas), eVect);
    NewMat:=NullMat(n,n);
    for jLine in [1..DimSpace]
    do
      NewMat:=NewMat + eSol[jLine]*Basis[jLine];
    od;
    Add(NewBasis, NewMat);
  od;
  if IsTspaceBasisIntegral(NewBasis)=false then
    Error("Bug in the integral basis computation");
  fi;
  return NewBasis;
end;





IsQuadFormIntegralValued:=function(eMat)
  local n, i, j;
  n:=Length(eMat);
  for i in [1..n]
  do
    if IsInt(eMat[i][i])=false then
      return false;
    fi;
  od;
  for i in [1..n-1]
  do
    for j in [i+1..n]
    do
      if IsInt(2*eMat[i][j])=false then
        return false;
      fi;
    od;
  od;
  return true;
end;



MatrixTestBelonging:=function(TheBasis, TestMatrix)
  local ListVector, test;
  ListVector:=List(TheBasis, SymmetricMatrixToVector);
  test:=SolutionMat(ListVector, SymmetricMatrixToVector(TestMatrix));
  if test=fail then
    return false;
  fi;
  return true;
end;


#
#
# test if the matrix U globally stabilizes the space define
# by Basis under the action M  -> U M t(U)
__IsGlobalSpaceStabilizer:=function(TheBasis, U)
  return First(TheBasis, x->MatrixTestBelonging(TheBasis, U*x*TransposedMat(U))=false)=fail;
end;



AffineExtensionPreservingCosetStructure:=function(ListCosets, eRepr)
  local n, eCos, fCos, eTrans, eAppl, ThePos;
  n:=Length(ListCosets[1])-1;
  eCos:=ListCosets[1];
  for fCos in ListCosets
  do
    eTrans:=fCos{[2..n+1]}-eCos{[2..n+1]};
    eAppl:=FuncCreateBigMatrix(eTrans, eRepr);
    ThePos:=First(ListCosets, x->Position(ListCosets, PeriodicVectorMod1(x*eAppl))=fail);
    if ThePos=fail then
      return eAppl;
    fi;
  od;
  return false;
end;



PersoRightCosets:=function(CharacteristicFamilyVector, GrpChar, SubGrp)
  local FuncMapToPerm, ListMatGen1, ListMatGen2, ListPermGen1, ListPermGen2, PermGrp1, PermGrp2, phi;
  FuncMapToPerm:=function(eMat)
    return PermList(List(CharacteristicFamilyVector, x->Position(CharacteristicFamilyVector, x*eMat)));
  end;
  ListMatGen1:=GeneratorsOfGroup(GrpChar);
  ListMatGen2:=GeneratorsOfGroup(SubGrp);
  ListPermGen1:=List(ListMatGen1, FuncMapToPerm);
  if Position(ListPermGen1, fail)<>fail then
    return fail;
  fi;
  ListPermGen2:=List(ListMatGen2, FuncMapToPerm);
  PermGrp1:=Group(ListPermGen1);
  PermGrp2:=Group(ListPermGen2);
  phi:=GroupHomomorphismByImagesNC(PermGrp1, GrpChar, ListPermGen1, ListMatGen1);
  return List(RightCosetsNC(PermGrp1, PermGrp2), x->Image(phi, Representative(x)));
end;



BasicCoherencyCheckups:=function(eCase)
  local eGen, eMat, eMatImg, BasisProj, eList, eSol;
  if IsBound(eCase.SymmGrpPtWs) then
    for eGen in GeneratorsOfGroup(eCase.SymmGrpPtWs)
    do
      if IsIntegralMat(eGen)=false then
        PrintArray(eGen);
        Error("The matrix generators of SymmGrpPtWs must be integral");
      fi;
      for eMat in eCase.Basis
      do
        eMatImg:=eGen * eMat * TransposedMat(eGen);
        if eMat<>eMatImg then
          Error("The matrix generators of SymmGrpPtWs must stabilize identically the basis");
        fi;
      od;
    od;
  fi;
  if IsBound(eCase.SymmGrpGlob) then
    Print("Checking SymmGrpGlob\n");
    BasisProj:=List(eCase.Basis, SymmetricMatrixToVector);
    for eGen in GeneratorsOfGroup(eCase.SymmGrpGlob)
    do
      if IsIntegralMat(eGen)=false then
        PrintArray(eGen);
        Error("The matrix generators of SymmGrpGlob must be integral");
      fi;
      for eMat in eCase.Basis
      do
        eMatImg:=eGen * eMat * TransposedMat(eGen);
        eSol:=SolutionMat(BasisProj, SymmetricMatrixToVector(eMatImg));
        if eSol=fail then
          Error("The matrix generators of SymmGrpGlob must stabilize globally the T-space");
        fi;
      od;
    od;
  fi;
  if IsBound(eCase.CharacteristicFamilyVector) then
    if RankMat(eCase.CharacteristicFamilyVector)<>Length(eCase.SuperMat) then
      Error("The characteristic family of vectors is not full-dimensional");
    fi;
    for eGen in GeneratorsOfGroup(eCase.SymmGrpPtWs)
    do
      eList:=List(eCase.CharacteristicFamilyVector, x->Position(eCase.CharacteristicFamilyVector, x*eGen));
      if Position(eList, fail)<>fail then
        Error("The characteristic family is not invariant by the group");
      fi;
    od;
  fi;
  for eMat in eCase.Basis
  do
    for eGen in GeneratorsOfGroup(eCase.SymmGrpPtWs)
    do
      if eMat<>eGen*eMat*TransposedMat(eGen) then
        Error("A matrix is not invariant under specified group");
      fi;
    od;
  od;
  if MatrixTestBelonging(eCase.Basis, eCase.SuperMat)=false then
    Error("The SuperMat does not belong to the space");
  fi;
  if IsPositiveDefiniteSymmetricMatrix(eCase.SuperMat)=false then
    Error("The SuperMat is not positive definite");
  fi;
end;



IsNormalizingTspace:=function(TheBasis, TheGen)
  local TheBasisImage, TheBasisImageExpand, TheBasisExpand, eVect, eSol;
  TheBasisImage:=List(TheBasis, x->TheGen*x*TransposedMat(TheGen));
  TheBasisImageExpand:=List(TheBasisImage, SymmetricMatrixToVector);
  TheBasisExpand:=List(TheBasis, SymmetricMatrixToVector);
  for eVect in TheBasisImageExpand
  do
    eSol:=SolutionMat(TheBasisExpand, eVect);
    if eSol=fail then
      return false;
    fi;
  od;
  return true;
end;


#
# TheBasis is a basis of elements of the invariant space under a group
# GramMat is the invariant Gram Matrix of a maximal representent
# It is also necessary that its symmetry group is equal to the symmetry
# group of 
RandomPositiveElement:=function(eCase)
  local TheSum, eMat, TheSpread;
  TheSum:=0;
  TheSpread:=30;
  for eMat in eCase.Basis
  do
    TheSum:=TheSum+Random([-TheSpread..TheSpread])*eMat;
  od;
  while(true)
  do
    if IsPositiveDefiniteSymmetricMatrix(TheSum)=true then
      break;
    else
      TheSum:=TheSum+eCase.SuperMat;
    fi;
  od;
  return TheSum;
end;


RandomPositiveElementFixedSymmetry:=function(eCase)
  local TheMat, GRP;
  while(true)
  do
    TheMat:=RandomPositiveElement(eCase);
    GRP:=ArithmeticAutomorphismGroup([TheMat]);
    if Order(GRP)=Order(eCase.SymmGrpPtWs) then
      return TheMat;
    fi;
  od;
end;





#
#
# We put as argument the list of matrices defining
# a matrix space
# GramMat should belong to that space and be positive definite
# the output is a generating list of the group of matrices
# satisfying to U*eMat*TransposedMat(U)=eMat
# LowerBound is a matrixGroup
__FindFullSymmetrySpace:=function(eCase, LowerBound)
  local AutGrp, eMat, GRP, ListGram, FuncTransform, IsSymmetry;
  IsSymmetry:=function(OneGroup)
    local eGen, lMat;
    for lMat in eCase.Basis
    do
      for eGen in GeneratorsOfGroup(OneGroup)
      do
        if eGen*lMat*TransposedMat(eGen)<>lMat then
          return false;
        fi;
      od;
    od;
    return true;
  end;
  ListGram:=[];
  while(true)
  do
    eMat:=RandomPositiveElement(eCase);
    Add(ListGram, eMat);
    GRP:=ArithmeticAutomorphismGroup(ListGram);
    if Order(GRP)=Order(LowerBound) then
      return LowerBound;
    fi;
    if IsSymmetry(GRP)=true then
      return GRP;
    fi;
  od;
end;


FindFullSymmetrySpace:=function(eCase)
  local n, LowerBound;
  n:=Length(eCase.SuperMat);
  LowerBound:=Group([-IdentityMat(n)]);
  return __FindFullSymmetrySpace(eCase, LowerBound);
end;


POLYDEC_HasConeNonVoidIntersection:=function(eCase, ListInequalities)
  local dimSpace, ListTestInequality, len, eIneq, ToBeMinimized, TheLP, fIneq, eVect, eEnt, vVect;
  dimSpace:=Length(eCase.Basis);
  ListTestInequality:=[];
  ToBeMinimized:=ListWithIdenticalEntries(dimSpace+1, 0);
  for eIneq in ListInequalities
  do
    if Length(eIneq)<>dimSpace then
      Error("We need to have eIneq of length dimSpace");
    fi;
    fIneq:=Concatenation([-1], eIneq);
    Add(ListTestInequality, fIneq);
    fIneq:=Concatenation([0], eIneq);
    ToBeMinimized:=ToBeMinimized+fIneq;
  od;
  for eIneq in eCase.ListFacets
  do
    fIneq:=Concatenation([-1], eIneq);
    Add(ListTestInequality, fIneq);
    fIneq:=Concatenation([0], eIneq);
    ToBeMinimized:=ToBeMinimized+fIneq;
  od;
  TheLP:=LinearProgramming(ListTestInequality, ToBeMinimized);
  if IsBound(TheLP.primal_solution) then
    eVect:=ListWithIdenticalEntries(dimSpace+1,0);
    for eEnt in TheLP.primal_solution
    do
      eVect[eEnt[1]]:=eEnt[2];
    od;
    for eIneq in ListInequalities
    do
      if eIneq*eVect<=0 then
        Error("There is incoherence here");
      fi;
    od;
    return true;
  else
    return false;
  fi;
end;



TSPACE_GetExtremeRayFunctions_V1:=function(eCase)
  local ListImagesExtRay, DimSpace, n, eEXT, eMat, i, ListPermGens, ListMatrGens, eGen, eList, PermGrpExtRays, phiExtRay, InvGlobInvMat, GetExtRaySignature, eImg, pos;
  ListImagesExtRay:=[];
  DimSpace:=Length(eCase.Basis);
  n:=Length(eCase.Basis[1]);
  for eEXT in eCase.ListExtRays
  do
    eMat:=NullMat(n,n);
    for i in [1..DimSpace]
    do
      eMat:=eMat+eEXT[i]*eCase.Basis[i];
    od;
    Add(ListImagesExtRay, RemoveFractionMatrix(eMat));
  od;
  ListPermGens:=[];
  ListMatrGens:=GeneratorsOfGroup(eCase.SymmGrpGlob);
  for eGen in ListMatrGens
  do
    eList:=[];
    for eMat in ListImagesExtRay
    do
      eImg:=RemoveFractionMatrix(eGen*eMat*TransposedMat(eGen));
      pos:=Position(ListImagesExtRay, eImg);
      if pos=fail then
        Error("Problem in creation of images of point");
      fi;
      Add(eList, pos);
    od;
#    Print("eList=", eList, "\n");
    Add(ListPermGens, PermList(eList));
  od;
  PermGrpExtRays:=Group(ListPermGens);
  phiExtRay:=GroupHomomorphismByImagesNC(eCase.SymmGrpGlob, PermGrpExtRays, ListMatrGens, ListPermGens);
  InvGlobInvMat:=Inverse(eCase.GlobInvarMat);
  GetExtRaySignature:=function(eMat)
    local ListScal, fMat;
    ListScal:=[];
    for fMat in ListImagesExtRay
    do
      Add(ListScal, Trace(fMat*InvGlobInvMat*eMat*InvGlobInvMat));
    od;
    return ListScal;
  end;
  return rec(PermGrpExtRays:=PermGrpExtRays,
             phiExtRay:=phiExtRay, 
             GetExtRaySignature:=GetExtRaySignature,
             ListImagesExtRay:=ListImagesExtRay);
end;


TSPACE_GetExtremeRayFunctions:=function(eCase)
  local ListImagesExtRay, DimSpace, n, eEXT, eMat, i, ListPermGens, ListMatrGens, eGen, eList, PermGrpExtRays, phiExtRay, InvGlobInvMat, GetExtRaySignature, eImg, pos, TheAct1, TheAct2, nbRay, BasisProj, ListStat, ListImagesExtRayCanonicalized, iStat, eO1, eO2, eO2nofrac, iMat, eMatNofrac, ListExtRaysCanonicalized, Qmat, ePermGen, j, iImg, jImg, eScal, fScal;
  DimSpace:=Length(eCase.Basis);
  n:=Length(eCase.Basis[1]);
  nbRay:=Length(eCase.ListExtRays);
  BasisProj:=List(eCase.Basis, SymmetricMatrixToVector);
  ListImagesExtRay:=[];
  for eEXT in eCase.ListExtRays
  do
    eMat:=NullMat(n,n);
    for i in [1..DimSpace]
    do
      eMat:=eMat+eEXT[i]*eCase.Basis[i];
    od;
    Add(ListImagesExtRay, RemoveFractionMatrix(eMat));
  od;
  TheAct1:=function(x, g)
    return RemoveFractionMatrix(g * x * TransposedMat(g));
  end;
  TheAct2:=function(x, g)
    return g * x * TransposedMat(g);
  end;
  # We build a canonical representation of the extreme rays
  ListStat:=ListWithIdenticalEntries(nbRay, 1);
  ListImagesExtRayCanonicalized:=[];
  for iStat in [1..nbRay]
  do
    if ListStat[iStat]=1 then
      eO1:=Orbit(eCase.SymmGrpGlob, ListImagesExtRay[iStat], TheAct1);
      eO2:=Orbit(eCase.SymmGrpGlob, ListImagesExtRay[iStat], TheAct2);
      if Length(eO1)<>Length(eO2) then
        Error("Assumption is broken 1http://mathieudutour.altervista.org/");
      fi;
      eO2nofrac:=List(eO2, RemoveFractionMatrix);
      if Set(eO2nofrac)<>Set(eO1) then
        Error("Assumption is broken 2");
      fi;
      for iMat in [1..Length(eO2)]
      do
        eMatNofrac:=eO2nofrac[iMat];
	eMat:=eO2[iMat];
        pos:=Position(ListImagesExtRay, eMatNofrac);
	ListImagesExtRayCanonicalized[pos]:=eMat;
      od;
    fi;
  od;
  ListExtRaysCanonicalized:=List(ListImagesExtRayCanonicalized, x->SolutionMat(BasisProj, SymmetricMatrixToVector(x)));
  ListPermGens:=[];
  ListMatrGens:=GeneratorsOfGroup(eCase.SymmGrpGlob);
  for eGen in ListMatrGens
  do
    eList:=[];
    for eMat in ListImagesExtRayCanonicalized
    do
      eImg:=eGen*eMat*TransposedMat(eGen);
      pos:=Position(ListImagesExtRayCanonicalized, eImg);
      if pos=fail then
        Error("Problem in creation of images of point");
      fi;
      Add(eList, pos);
    od;
    Add(ListPermGens, PermList(eList));
  od;
  PermGrpExtRays:=Group(ListPermGens);
  Qmat:=poly_private@Get_QinvMatrix(ListExtRaysCanonicalized);
  for ePermGen in ListPermGens
  do
    for i in [1..nbRay]
    do
      for j in [1..nbRay]
      do
        iImg:=OnPoints(i, ePermGen);
        jImg:=OnPoints(j, ePermGen);
	eScal:=ListExtRaysCanonicalized[i]*Qmat*ListExtRaysCanonicalized[j];
	fScal:=ListExtRaysCanonicalized[iImg]*Qmat*ListExtRaysCanonicalized[jImg];
	if eScal<>fScal then
	  Error("We have inconsistency in scalar product");
	fi;
      od;
    od;
  od;
  phiExtRay:=GroupHomomorphismByImagesNC(eCase.SymmGrpGlob, PermGrpExtRays, ListMatrGens, ListPermGens);
  GetExtRaySignature:=function(eMat)
    local ListScal, eExpr, eV;
    ListScal:=[];
    eExpr:=SolutionMat(BasisProj, SymmetricMatrixToVector(eMat));
    for eV in ListExtRaysCanonicalized
    do
      eScal:=eExpr * Qmat * eV;
      Add(ListScal, eScal);
    od;
    return ListScal;
  end;
  return rec(PermGrpExtRays:=PermGrpExtRays,
             phiExtRay:=phiExtRay, 
             GetExtRaySignature:=GetExtRaySignature,
             ListImagesExtRay:=ListImagesExtRay);
end;

