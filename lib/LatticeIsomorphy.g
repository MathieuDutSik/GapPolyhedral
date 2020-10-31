#FileIsom:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"isom");
#FileAutom:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"autom");
FileISOM:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"ISOM");
FileAUTO:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"AUTO");
#FileISOM32:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"ISOM32");
#FileAUTO32:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"AUTO32");
#FileISOM64:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"ISOM64");
#FileAUTO64:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"AUTO64");
FileISOM32:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"ISOM");
FileAUTO32:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"AUTO");
FileISOM64:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"ISOM");
FileAUTO64:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"AUTO");
FileISOMtoGAP:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"ISOMtoGAP");
FileAUTOMtoGAP:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"AUTOMtoGAP");
FileMatrix_TYP_Aut_Grp:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"Matrix_TYP_AutGrp_to_GAP");
FileIsometry:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"Isometry");
FileZ_equiv:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"Z_equiv");
FileZ_equiv_toGAP:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"Z_equiv_toGAP");
FileAutoVectorFamily:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"AutomorphismGroupVectorFamily");

SuccessiveMinima_DirectMethod:=function(GramMat)
  local n, TheDiag, TheMax, SHV;
  if IsPositiveDefiniteSymmetricMatrix(GramMat)=false then
    Error("The matrix is not positive definite");
  fi;
  n:=Length(GramMat);
  TheDiag:=List([1..n], x->GramMat[x][x]);
  TheMax:=Maximum(TheDiag);
  SHV:=ShortestVectors(GramMat, TheMax);
  return Set(SHV.norms);
end;

# we get a upper estimation but the price is much smaller
SuccessiveMinima_Superset:=function(GramMat)
  local n, TheDiag, TheMax, TheMin, SHV;
  if IsPositiveDefiniteSymmetricMatrix(GramMat)=false then
    Error("The matrix is not positive definite");
  fi;
  n:=Length(GramMat);
  TheDiag:=List([1..n], x->GramMat[x][x]);
  TheMax:=Maximum(TheDiag);
  SHV:=ShortestVectorDutourVersion(GramMat);
  TheMin:=Minimum(List(SHV, x->x*GramMat*x));
  return [TheMin..TheMax];
end;



__FrameworkExtractionSpecialInvariantBasis:=function(GramMat, PointGRP, IsBetterProperty, IsWishedSet)
  local n, EWR, rnkEWR, LNorm, posNorm, SHV, ListVector, CurrentNorm, Lcons, iV, LOrb, eOrb, eV, ListMinimaUpper;
  n:=Length(GramMat);
  if IsIntegralMat(GramMat)=false then
    Error("The Input matrix should be integral");
  fi;
  ListVector:=[];
  if n<=4 then
    ListMinimaUpper:=SuccessiveMinima_DirectMethod(GramMat);
  else
    ListMinimaUpper:=SuccessiveMinima_Superset(GramMat);
  fi;
  posNorm:=1;
  CurrentNorm:=ListMinimaUpper[posNorm];
  SHV:=ShortestVectors(GramMat, CurrentNorm);
  while(true)
  do
    Lcons:=[];
    for iV in [1..Length(SHV.vectors)]
    do
      if SHV.norms[iV]=CurrentNorm then
        eV:=SHV.vectors[iV];
        Add(Lcons, eV);
        Add(Lcons, -eV);
      fi;
    od;
    LOrb:=Orbits(PointGRP, Lcons, OnPoints);
    for eOrb in LOrb
    do
      EWR:=Union(Set(ListVector), Set(eOrb));
      if IsBetterProperty(EWR, ListVector)=true then
        Append(ListVector, eOrb);
      fi;
      if IsWishedSet(ListVector)=true then
        return ListVector;
      fi;
    od;
    posNorm:=posNorm+1;
    CurrentNorm:=ListMinimaUpper[posNorm];
    SHV:=ShortestVectors(GramMat, CurrentNorm);
  od;
end;




__ExtractInvariantFaithfulFamilyShortVector_Rational:=function(GramMat, MatrixGrp)
  local n, OrdGRP, OrderPermGRP, IsBetterProperty, IsWishedSet, SVR, ListPermGens, WorkGramMat;
  n:=Length(GramMat);
  WorkGramMat:=RemoveFractionMatrix(GramMat);
  OrdGRP:=Size(MatrixGrp);
  OrderPermGRP:=function(InvSet)
    return Order(PersoGroupPerm(List(GeneratorsOfGroup(MatrixGrp), x->PermList(List(InvSet, y->Position(InvSet, y*x))))));
  end;
  IsBetterProperty:=function(NewSet, OldSet)
    local ordGRPnew, ordGRPold;
    ordGRPnew:=OrderPermGRP(NewSet);
    ordGRPold:=OrderPermGRP(OldSet);
    if ordGRPnew>ordGRPold then
      return true;
    else
      return false;
    fi;
  end;
  IsWishedSet:=function(TheSet)
    local TheOrd;
    TheOrd:=OrderPermGRP(TheSet);
    if TheOrd>OrdGRP then
      Error("There is an illogicness here");
    fi;
    if TheOrd=OrdGRP then
      return true;
    else
      return false;
    fi;
  end;
  return __FrameworkExtractionSpecialInvariantBasis(WorkGramMat, MatrixGrp, IsBetterProperty, IsWishedSet);
end;












__ExtractInvariantZBasisShortVectorNoGroupGeneral:=function(GramMat, SHVgroup)
  local n, IsBetterProperty, IsWishedSet, ListVector, EWR, eSHV;
  n:=Length(GramMat);
  IsBetterProperty:=function(NewSet, OldSet)
    local rNew, rOld, detNew, detOld, eSelect, NewSetProj, OldSetProj;
    rNew:=ZeroRankMat(NewSet);
    rOld:=ZeroRankMat(OldSet);
    if rNew>rOld then
      return true;
    fi;
    if rNew=n then
      eSelect:=[1..n];
    else
      eSelect:=ColumnReduction(NewSet).Select;
    fi;
    NewSetProj:=List(NewSet, x->x{eSelect});
    OldSetProj:=List(OldSet, x->x{eSelect});
    detNew:=AbsInt(DeterminantMat(BaseIntMat(NewSetProj)));
    detOld:=AbsInt(DeterminantMat(BaseIntMat(OldSetProj)));
    if detNew<detOld then
      return true;
    fi;
    return false;
  end;
  IsWishedSet:=function(TheSet)
    local det;
    if ZeroRankMat(TheSet)<n then
      return false;
    fi;
    det:=AbsInt(DeterminantMat(BaseIntMat(TheSet)));
    if det=1 then
      return true;
    fi;
    return false;
  end;
  ListVector:=[];
  for eSHV in SHVgroup
  do
    EWR:=Concatenation(ListVector, eSHV);
    if IsBetterProperty(EWR, ListVector)=true then
      Append(ListVector, eSHV);
    fi;
    if IsWishedSet(ListVector)=true then
      if Length(ListVector)<>Length(Set(ListVector)) then
        Error("This is not correct");
      fi;
      return ListVector;
    fi;
  od;
  Error("We should NOT reach that stage");
end;



__ExtractInvariantZBasisShortVectorNoGroupGeneralLazy:=function(GramMat, GetSHVgroup, DoExpansion)
  local n, IsBetterProperty, IsWishedSet, ListVector, EWR, eSHV, posSHV, SHVgroup;
  n:=Length(GramMat);
  IsBetterProperty:=function(NewSet, OldSet)
    local rNew, rOld, detNew, detOld, eSelect, NewSetProj, OldSetProj;
    rNew:=ZeroRankMat(NewSet);
    rOld:=ZeroRankMat(OldSet);
    if rNew>rOld then
      return true;
    fi;
    if rNew=n then
      eSelect:=[1..n];
    else
      eSelect:=ColumnReduction(NewSet).Select;
    fi;
    NewSetProj:=List(NewSet, x->x{eSelect});
    OldSetProj:=List(OldSet, x->x{eSelect});
    detNew:=AbsInt(DeterminantMat(BaseIntMat(NewSetProj)));
    detOld:=AbsInt(DeterminantMat(BaseIntMat(OldSetProj)));
    if detNew<detOld then
      return true;
    fi;
    return false;
  end;
  IsWishedSet:=function(TheSet)
    local det;
    if ZeroRankMat(TheSet)<n then
      return false;
    fi;
    det:=AbsInt(DeterminantMat(BaseIntMat(TheSet)));
    if det=1 then
      return true;
    fi;
    return false;
  end;
  ListVector:=[];
  SHVgroup:=[];
  posSHV:=0;
  while(true)
  do
    posSHV:=posSHV+1;
    if posSHV>Length(SHVgroup) then
      DoExpansion();
      SHVgroup:=GetSHVgroup();
    fi;
    eSHV:=SHVgroup[posSHV];
    EWR:=Concatenation(ListVector, eSHV);
    if IsBetterProperty(EWR, ListVector)=true then
      Append(ListVector, eSHV);
    fi;
    if IsWishedSet(ListVector)=true then
      if Length(ListVector)<>Length(Set(ListVector)) then
        Error("This is not correct");
      fi;
      return ListVector;
    fi;
  od;
end;



GetReducedDiagonal:=function(GramMat)
  local n, WorkGramMat, RedGramMat, TheDiag;
  n:=Length(GramMat);
  WorkGramMat:=RemoveFractionMatrix(GramMat);
  RedGramMat:=LLLReducedGramMat(WorkGramMat).remainder;
  TheDiag:=List([1..n], x->RedGramMat[x][x]);
  return TheDiag;
end;

GetIndexVectorFamily:=function(LVect)
  return AbsInt(DeterminantMat(BaseIntMat(LVect)));
end;


__ExtractInvariantZBasisShortVectorNoGroup_V1:=function(GramMat)
  local n, WorkGramMat, LNorm, SHV, ListVector, ListNorms, eNorm, eSHV, iV, SHVgroup, TheDet, eSet, ListInv, eEnt, GetFctInvariant, TheColl, iNorm, DoExpansion, GetSHVgroup, TheDiag;
  if IsPositiveDefiniteSymmetricMatrix(GramMat)=false then
    Print("Error in __ExtractInvariantZBasisShortVectorNoGroup\n");
    Error("The matrix should be positive definite");
  fi;
  n:=Length(GramMat);
  WorkGramMat:=RemoveFractionMatrix(GramMat);
  TheDiag:=GetReducedDiagonal(GramMat);
#  Print("TheDiag=", TheDiag, "\n");
  LNorm:=Set(TheDiag);
  SHV:=ShortestVectors(WorkGramMat, Maximum(LNorm));
#  Print("|SHV.norms|=", Length(SHV.norms), " Coll=", Collected(SHV.norms), "\n");
  ListVector:=[];
  ListNorms:=Set(SHV.norms);
  TheDet:=Determinant(BaseIntMat(SHV.vectors));
  if AbsInt(TheDet)<>1 then
    Error("We have an inconsistency in determinant");
  fi;
  SHVgroup:=[];
  GetFctInvariant:=function(SHVgroup, eVect)
    return List(SHVgroup, y->Collected(List(y, x->x*WorkGramMat*eVect)));
  end;
  iNorm:=0;
  DoExpansion:=function()
    iNorm:=iNorm+1;
    eNorm:=ListNorms[iNorm];
#    Print("iNorm=", iNorm, " eNorm=", eNorm, "\n");
    eSHV:=[];
    for iV in [1..Length(SHV.norms)]
    do
      if SHV.norms[iV]=eNorm then
        Add(eSHV, SHV.vectors[iV]);
        Add(eSHV, -SHV.vectors[iV]);
      fi;
    od;
    if Length(SHVgroup)=1 then
      ListInv:=ListWithIdenticalEntries(Length(eSHV), eNorm);
    else
      ListInv:=List(eSHV, x->GetFctInvariant(SHVgroup, x));
    fi;
    TheColl:=Collected(ListInv);
    for eEnt in TheColl
    do
      eSet:=Filtered([1..Length(ListInv)], x->ListInv[x]=eEnt[1]);
      Add(SHVgroup, eSHV{eSet});
    od;
    Add(SHVgroup, eSHV);
  end;
  GetSHVgroup:=function()
    return SHVgroup;
  end;
  return __ExtractInvariantZBasisShortVectorNoGroupGeneralLazy(WorkGramMat, GetSHVgroup, DoExpansion);
end;


# Takes a family of vectors and returns the saturation span
# of this family.
# So SatSpan([[2,0]]) = [[1,0]]
SaturationSpan:=function(ListVect)
  local TheOrth;
  TheOrth:=RemoveFractionMatrix(NullspaceMat(TransposedMat(ListVect)));
  return NullspaceIntMat(TransposedMat(TheOrth));
end;


# We are in a situation where we had vectors one by one.
# This incremental approach should allow a limitation of
# combinatorial explosion.
__ExtractInvariantZBasisShortVectorNoGroup_UsingCVP:=function(GramMat)
  local SHVreturn, TheSpann, TheSub, TheOrth, n, GetOneFamily, GetOrth, TheProjection, GetRelevantPointSet, TheSubProj, GramProj, eRec, eVect, eVectEmbed;
  SHVreturn:=[];
  TheSpann:=[];
  TheSub:=[];
  TheOrth:=[];
  n:=Length(GramMat);
  # We take a family of shortest vectors,
  # consider the lattice spanned by it and
  #
  GetOneFamily:=function(eG)
    local eGred, SHV, TheSpace, TheOrth, eG2, SHVspann, SHVspannB;
    eGred:=RemoveFractionMatrix(eG);
    SHV:=ShortestVectorDutourVersion(eGred);
    if RankMat(SHV)=Length(eG) then
      TheSpace:=IdentityMat(Length(eG));
    else
      TheSpace:=SaturationSpan(SHV);
    fi;
    eG2:=TheSpace * eG * TransposedMat(TheSpace);
    SHVspann:=__ExtractInvariantZBasisShortVectorNoGroup_V1(eG2);
    SHVspannB:=SHVspann*TheSpace;
    return rec(SHVspann:=SHVspann, SHVspannB:=SHVspannB, TheSpace:=TheSpace);
  end;
  GetOrth:=function(uSpann)
    local TheProd;
    if Length(uSpann)=0 then
      return IdentityMat(n);
    fi;
    TheProd:=uSpann * GramMat;
    return NullspaceIntMat(TransposedMat(RemoveFractionMatrix(TheProd)));
  end;
  TheProjection:=function(eVector)
    local TheConcat, eSol, TheReturn, i, eCoeff;
    TheConcat:=Concatenation(TheSpann, TheOrth);
    eSol:=SolutionMat(TheConcat, eVector);
    TheReturn:=ListWithIdenticalEntries(n, 0);
    for i in [1..Length(TheOrth)]
    do
      eCoeff:=eSol[Length(TheSpann) + i];
      TheReturn:=TheReturn + eCoeff * TheOrth[i];
    od;
    return TheReturn;
  end;
  GetRelevantPointSet:=function(eVEmbed)
    local TheConcat, eSol, eSolSpann, eSolSub, eGspann, RecCVP, ListReturn, eV, eVfull;
    if Length(TheSpann)=0 then
      if IsIntegralVector(eVEmbed)=false then
        Error("Vector should be integral");
      fi;
      return [eVEmbed];
    fi;
    TheConcat:=Concatenation(TheSpann, TheSub);
    eSol:=SolutionMat(TheConcat, eVEmbed);
    eSolSpann:=eSol{[1..Length(TheSpann)]};
    eSolSub:=eSol{[1+Length(TheSpann)..n]};
    if IsIntegralVector(eSolSub)=false then
      Error("The vector eSolSub should be integral");
    fi;
    eGspann:=TheSpann * GramMat * TransposedMat(TheSpann);
    RecCVP:=CVPVallentinProgram(eGspann, eSolSpann);
    ListReturn:=[];
    for eV in RecCVP.ListVect
    do
      eVfull:=eV * TheSpann + eSolSub * TheSub;
      Add(ListReturn, eVfull);
    od;
    return ListReturn;
  end;
  while(true)
  do
    TheSub:=SubspaceCompletion(TheSpann, n);
    TheOrth:=GetOrth(TheSpann);
    TheSubProj:=List(TheSub, TheProjection);
    GramProj:=TheSubProj * GramMat * TransposedMat(TheSubProj);
    eRec:=GetOneFamily(GramProj);
    for eVect in eRec.SHVspannB
    do
      eVectEmbed:=eVect * TheSubProj;
      Append(SHVreturn, GetRelevantPointSet(eVectEmbed));
    od;
    Append(TheSpann, eRec.TheSpace * TheSub);
    if Length(TheSpann)=n then
      break;
    fi;
  od;
  return SHVreturn;
end;


#__ExtractInvariantZBasisShortVectorNoGroup:=__ExtractInvariantZBasisShortVectorNoGroup_UsingCVP;
__ExtractInvariantZBasisShortVectorNoGroup:=__ExtractInvariantZBasisShortVectorNoGroup_V1;


#
#
# In principle, we can remove one more sorting operation here.
RetrieveListPermGensFromVectors:=function(SVR, ListGen)
  local SVRset, ePermSort, ListPermGens, eGen, ePermB, ePerm, ePermTest;
  ePermSort:=SortingPerm(SVR);
  SVRset:=Set(SVR);
  ListPermGens:=[];
  for eGen in ListGen
  do
    ePermB:=SortingPerm(SVRset*eGen);
    ePerm:=ePermSort*ePermB*Inverse(ePermSort);
#    ePermTest:=PermList(List(SVR, x->Position(SVR, x*eGen)));
#    if ePerm<>ePermTest then
#      Error("Wrong formula for ePerm");
#    fi;
    Add(ListPermGens, ePerm);
  od;
#  Print("We got the permutations\n");
#  Print(NullMat(5));
  return ListPermGens;
end;

Kernel_ExtractInvariantFaithfulFamilyShortVector:=function(GramMat, MatrixGrp)
  if IsMatrixRational(GramMat)=true then
    return __ExtractInvariantFaithfulFamilyShortVector_Rational(GramMat, MatrixGrp);
  fi;
  Error("Put your arithmetic here");
end;


__ExtractInvariantFaithfulFamilyShortVector:=function(GramMat, MatrixGrp)
  local SVR;
  SVR:=Kernel_ExtractInvariantFaithfulFamilyShortVector(GramMat, MatrixGrp);
#  Print("|SVR|=", Length(SVR), "\n");
  return rec(SVR:=SVR,
             ListPermGens:=RetrieveListPermGensFromVectors(SVR, GeneratorsOfGroup(MatrixGrp)));
end;


__ExtractInvariantZBasisShortVector_Rational:=function(GramMat, PointGRP)
  local eGen, IsBetterProperty, IsWishedSet, n, WorkGramMat;
  WorkGramMat:=RemoveFractionMatrix(GramMat);
  for eGen in GeneratorsOfGroup(PointGRP)
  do
    if eGen*WorkGramMat*TransposedMat(eGen)<>WorkGramMat then
      Error("You are not correct. Matrix is not invariant");
    fi;
  od;
  n:=Length(GramMat);
  IsBetterProperty:=function(NewSet, OldSet)
    local rNew, rOld, detNew, detOld, eSelect, NewSetProj, OldSetProj;
    rNew:=ZeroRankMat(NewSet);
    rOld:=ZeroRankMat(OldSet);
    if rNew>rOld then
      return true;
    fi;
    if rNew=n then
      eSelect:=[1..n];
    else
      eSelect:=ColumnReduction(NewSet).Select;
    fi;
    NewSetProj:=List(NewSet, x->x{eSelect});
    OldSetProj:=List(OldSet, x->x{eSelect});
    detNew:=AbsInt(DeterminantMat(BaseIntMat(NewSetProj)));
    detOld:=AbsInt(DeterminantMat(BaseIntMat(OldSetProj)));
    if detNew<detOld then
      return true;
    fi;
    return false;
  end;
  IsWishedSet:=function(TheSet)
    local det;
    if ZeroRankMat(TheSet)<n then
      return false;
    fi;
    det:=AbsInt(DeterminantMat(BaseIntMat(TheSet)));
    if det=1 then
      return true;
    fi;
    return false;
  end;
  return __FrameworkExtractionSpecialInvariantBasis(WorkGramMat, PointGRP, IsBetterProperty, IsWishedSet);
end;



__ExtractInvariantZBasisShortVector:=function(GramMat, PointGRP)
  if IsMatrixRational(GramMat)=true then
    return __ExtractInvariantZBasisShortVector_Rational(GramMat, PointGRP);
  fi;
  Error("Please put your arithmetic here");
end;

KernelGetInvariantGram:=function(TheNewGram, SHVdisc)
  local eIntMat, eDet, ListValOff, ListNbOff, ListValDiag, ListNbDiag, nbSHV, eScal, pos, iSHV, jSHV, ePermOff, ePermDiag;
  eIntMat:=RemoveFractionMatrix(TheNewGram);
  eDet:=DeterminantMat(eIntMat);
  ListValOff:=[];
  ListNbOff:=[];
  ListValDiag:=[];
  ListNbDiag:=[];
  nbSHV:=Length(SHVdisc);
  for iSHV in [1..nbSHV]
  do
    eScal:=SHVdisc[iSHV]*eIntMat*SHVdisc[iSHV];
    pos:=Position(ListValDiag, eScal);
    if pos=fail then
      Add(ListValDiag, eScal);
      Add(ListNbDiag, 1);
    else
      ListNbDiag[pos]:=ListNbDiag[pos]+1;
    fi;
    for jSHV in [iSHV+1..nbSHV]
    do
      eScal:=SHVdisc[iSHV]*eIntMat*SHVdisc[jSHV];
      pos:=Position(ListValOff, eScal);
      if pos=fail then
        Add(ListValOff, eScal);
        Add(ListNbOff, 1);
      else
        ListNbOff[pos]:=ListNbOff[pos]+1;
      fi;
    od;
  od;
  ePermOff:=SortingPerm(ListValOff);
  ePermDiag:=SortingPerm(ListValDiag);
  return rec(eDet:=eDet,
             ListValOff:=Permuted(ListValOff, ePermOff),
             ListNbOff:=Permuted(ListNbOff, ePermOff),
             ListValDiag:=Permuted(ListValDiag, ePermDiag),
             ListNbDiag:=Permuted(ListNbDiag, ePermDiag));
end;

GetInvariantGram:=function(TheNewGram)
  local SHVdisc;
  SHVdisc:=__ExtractInvariantZBasisShortVectorNoGroup(TheNewGram);
  return KernelGetInvariantGram(TheNewGram, SHVdisc);
end;




DoesItContainStandardBasis:=function(SVR)
  local n, i, j, eSgn, TestVect;
  if Length(SVR)=0 then
    return false;
  fi;
  n:=Length(SVR[1]);
  for i in [1..n]
  do
    for j in [0..1]
    do
      eSgn:=2*j-1;
      TestVect:=ListWithIdenticalEntries(n, 0);
      TestVect[i]:=eSgn;
      if Position(SVR, TestVect)=fail then
        return false;
      fi;
    od;
  od;
  return true;
end;

GetStartingAffine:=function(SVR)
  local StartingAffine, i, eVect, pos, n;
  StartingAffine:=[];
  n:=Length(SVR[1]);
  for i in [1..n]
  do
    eVect:=ListWithIdenticalEntries(n,0);
    eVect[i]:=1;
    pos:=Position(SVR, eVect);
    if pos<>fail then
      Add(StartingAffine, eVect);
    fi;
  od;
  return StartingAffine;
end;

UseExistingForAffineBasis:=function(SVR)
  local StartingAffine, n;
  if DoesItContainStandardBasis(SVR)=true then
    n:=Length(SVR[1]);
    return IdentityMat(n);
  else
    StartingAffine:=GetStartingAffine(SVR);
    return ExtendToCompleteAffineBasis(SVR, StartingAffine);
#    return CreateAffineBasis(TheInvariantBase);
  fi;
end;



GetRecSVR:=function(GramMat, PointGRP)
  local n, TheInvariantBase, WorkingAffineBasis, SVRfaithful;
  n:=Length(GramMat);
  TheInvariantBase:=__ExtractInvariantZBasisShortVector(GramMat, PointGRP);
  WorkingAffineBasis:=UseExistingForAffineBasis(TheInvariantBase);
  SVRfaithful:=Kernel_ExtractInvariantFaithfulFamilyShortVector(GramMat, PointGRP);
  return rec(TheInvariantBase:=TheInvariantBase,
             WorkingAffineBasis:=WorkingAffineBasis,
             SVRfaithful:=SVRfaithful);
end;


#
# Computing automorphism group of lattices.
#


__FunctionOutPutMatrix_TYP:=function(FileName, ListGen)
  local output, n, iGen;
  output:=OutputTextFile(FileName, true);
  AppendTo(output, "#", Length(ListGen), "\n");
  n:=Length(ListGen[1]);
  for iGen in [1..Length(ListGen)]
  do
    AppendTo(output, n, "% generator\n");
    WriteMatrix(output, ListGen[iGen]);
  od;
  CloseStream(output);
end;







#
# return am integer matrix U such that
# U*SymMat1*TransposedMat(U)=SymMat2 if it exist and
# false otherwise.
Method1IsomorphyLattice:=function(SymMat1, SymMat2)
  local output, dim, iCol, jCol, FileIn, FileOut, FileGap, REP;
  FileIn:=Filename(POLYHEDRAL_tmpdir, "ISOM.in");
  FileOut:=Filename(POLYHEDRAL_tmpdir, "ISOM.out");
  FileGap:=Filename(POLYHEDRAL_tmpdir, "ISOM.gap");
  if IsPositiveDefiniteSymmetricMatrix(SymMat1)=false or IsPositiveDefiniteSymmetricMatrix(SymMat1)=false then
    Print("Matrices should be positive definite\n");
    return fail;
  fi;
  dim:=Length(SymMat1);
  output:=OutputTextFile(FileIn, true);;
  AppendTo(output, dim, "x", 0,"\n");
  for iCol in [1..dim]
  do
    for jCol in [1..iCol]
    do
      AppendTo(output, " ", SymMat1[iCol][jCol]);
    od;
    AppendTo(output, "\n");
  od;
  AppendTo(output, "\n");
  AppendTo(output, dim, "x", 0,"\n");
  for iCol in [1..dim]
  do
    for jCol in [1..iCol]
    do
      AppendTo(output, " ", SymMat2[iCol][jCol]);
    od;
    AppendTo(output, "\n");
  od;
  CloseStream(output);
  Exec(FileISOM, " ", FileIn, " > ", FileOut);
  Exec(FileISOMtoGAP, " ", FileOut, " > ", FileGap);
  REP:=ReadAsFunction(FileGap)();
  RemoveFile(FileIn);
  RemoveFile(FileOut);
  RemoveFile(FileGap);
  if REP=false then
    return false;
  else
    return Inverse(REP);
  fi;
end;

__RandomIntegralLU:=function(n)
  local SingleRandom, ite, TheMat, i;
  SingleRandom:=function()
    local M, H1, H2, val;
    M:=IdentityMat(n);
    H1:=Random([1..n]);
    H2:=Random(Difference([1..n], [H1]));
    val:=Random([-2..2]);
    M[H1][H2]:=val;
    return M;
  end;
  ite:=Random([1..100]);
  TheMat:=IdentityMat(n);
  for i in [1..ite]
  do
    TheMat:=TheMat*SingleRandom();
  od;
  return TheMat;
end;

# uses Bruhat decomposition
RandomIntegralGLnZmatrix:=function(n)
  local Mat1, Mat2, UniM, ePerm, i;
  Mat1:=__RandomIntegralLU(n);
  Mat2:=__RandomIntegralLU(n);
  ePerm:=Random(SymmetricGroup(n));
  UniM:=NullMat(n,n);
  for i in [1..n]
  do
    UniM[i][OnPoints(i, ePerm)]:=1;
  od;
  return Mat1*UniM*Mat2;
end;




FuncTestIsomorphyLattice:=function(SymMat1, SymMat2)
  local res1, res2, U1, U2, GramNew1, GramNew2, P;
  res1:=LLLReducedGramMat(SymMat1);
  res2:=LLLReducedGramMat(SymMat2);
  U1:=res1.transformation;
  U2:=res2.transformation;
  GramNew1:=res1.remainder;
  GramNew2:=res2.remainder;
  P:=Method1IsomorphyLattice(GramNew1, GramNew2);
  if P=false then
    return false;
  else
    return Inverse(U2)*P*U1;
  fi;
end;



IsSelfDualLattice:=function(GramMat)
  local GramMat1, GramMat2, test;
  GramMat1:=RemoveFractionMatrix(GramMat);
  GramMat2:=RemoveFractionMatrix(Inverse(GramMat));
  test:=FuncTestIsomorphyLattice(GramMat1, GramMat2);
  if test=false then
    return false;
  else
    return true;
  fi;
end;




AUTO_ISOM__PrintMatrix:=function(output, TheMat)
  local PrintLowMat, PrintTotalMat, n;
  n:=Length(TheMat);
  PrintLowMat:=function(TheMat)
    local i, j;
    for i in [1..n]
    do
      for j in [1..i]
      do
        AppendTo(output, " ", TheMat[i][j]);
      od;
      AppendTo(output, "\n");
    od;
  end;
  PrintTotalMat:=function(TheMat)
    local i, j;
    for i in [1..n]
    do
      for j in [1..n]
      do
        AppendTo(output, " ", TheMat[i][j]);
      od;
      AppendTo(output, "\n");
    od;
  end;
  if TheMat=TransposedMat(TheMat) then
    AppendTo(output, n, "x0\n");
    PrintLowMat(TheMat);
  elif TheMat=-TransposedMat(TheMat) then
    AppendTo(output, n, "x-1\n");
    PrintLowMat(TheMat);
  else
    AppendTo(output, n, "\n");
    PrintTotalMat(TheMat);
  fi;
end;




ArithmeticAutomorphismMatrixFamily_Souvignier:=function(TheOption, ListMat, SVR)
  local n, FileIn, FileOut, FileGap, FileError32, FileError64, output, eMat, eVect, i, TheNorm, ChainOption, REP, TheMatrixGRP, KeyTest, eGen, rListMat, TheMult, eRec, eLine, eEnt;
  n:=Length(ListMat[1]);
  if IsPositiveDefiniteSymmetricMatrix(ListMat[1])=false then
    Error("The first matrix should be positive definite");
  fi;
  TheMult:=1;
  for eMat in ListMat
  do
    for eLine in eMat
    do
      for eEnt in eLine
      do
        TheMult:=LcmInt(TheMult, DenominatorRat(eEnt));
      od;
    od;
  od;
  rListMat:=[];
  for eMat in ListMat
  do
    Add(rListMat, TheMult*eMat);
  od;
  FileIn:=Filename(POLYHEDRAL_tmpdir, "AUTO.in");
  FileOut:=Filename(POLYHEDRAL_tmpdir, "AUTO.out");
  FileGap:=Filename(POLYHEDRAL_tmpdir, "AUTO.gap");
  FileError32:=Filename(POLYHEDRAL_tmpdir, "AUTO.error32");
  FileError64:=Filename(POLYHEDRAL_tmpdir, "AUTO.error64");
  output:=OutputTextFile(FileIn, true);
  AppendTo(output, "#", Length(rListMat), "\n");
  for eMat in rListMat
  do
    AUTO_ISOM__PrintMatrix(output, eMat);
  od;
  ChainOption:="";
  KeyTest:=DoesItContainStandardBasis(SVR);
  if KeyTest=true then
    ChainOption:=" -V";
    AppendTo(output, "\n");
    AppendTo(output, Length(SVR), "\n");
    for eVect in SVR
    do
      for i in [1..n]
      do
        AppendTo(output, " ", eVect[i]);
      od;
      TheNorm:=eVect*rListMat[1]*eVect;
      AppendTo(output, " ", TheNorm, "\n");
    od;
  fi;
  CloseStream(output);
  # not completely satisfying here ...
  Exec(FileAUTO32, TheOption, ChainOption, " < ", FileIn, " > ", FileOut, "2>", FileError32);
#  Exec(FileAUTO64, TheOption, ChainOption, " < ", FileIn, " > ", FileOut, "2>", FileError);
  if IsEmptyFile(FileError32)=false then
    Print("Error at 32 bit arithmetic, trying 64 bits...\n");
    RemoveFile(FileOut);
    Exec(FileAUTO64, TheOption, ChainOption, " < ", FileIn, " > ", FileOut, "2>", FileError64);
    if IsEmptyFile(FileError64)=false then
      Error("Error also at 64 bits in ArithmeticAutomorphismMatrixFamily_Souvignier");
    fi;
  fi;
  Exec(FileAUTOMtoGAP, " ", FileOut, " > ", FileGap);
  REP:=ReadAsFunction(FileGap)();
  TheMatrixGRP:=Group(REP.ListMat);
  SetSize(TheMatrixGRP, REP.order);
  RemoveFile(FileIn);
  RemoveFile(FileOut);
  RemoveFile(FileGap);
  RemoveFile(FileError32);
  RemoveFile(FileError64);
  # just a check to be sure
  for eGen in GeneratorsOfGroup(TheMatrixGRP)
  do
    for eMat in ListMat
    do
      if eGen*eMat*TransposedMat(eGen)<>eMat then
        Error("We have an error in ArithmeticAutomorphismMatrixFamily_Souvignier");
      fi;
    od;
    if Set(SVR*eGen)<>Set(SVR) then
      Print("The SVR is not stabilized. This is a feature, not a bug.\n");
      Print("But likely not what you want.\n");
    fi;
  od;
  return TheMatrixGRP;
end;


ArithmeticAutomorphismMatrixFamily_HackSouvignier:=function(TheOption, ListMat, SVR, AffBas)
  local ListMatMapped, SVRMapped, TheGRP, GRPret, eGen, eMat;
  if IsPositiveDefiniteSymmetricMatrix(ListMat[1])=false then
    Error("The first matrix should be positive definite");
  fi;
  ListMatMapped:=List(ListMat, x->AffBas*x*TransposedMat(AffBas));
  if Length(SVR)=0 then
    SVRMapped:=[];
  else
    SVRMapped:=SVR*Inverse(AffBas);
  fi;
  TheGRP:=ArithmeticAutomorphismMatrixFamily_Souvignier(TheOption, ListMatMapped, SVRMapped);
  GRPret:=Group(List(GeneratorsOfGroup(TheGRP), x->Inverse(AffBas)*x*AffBas));
  SetSize(GRPret, Size(TheGRP));
  for eGen in GeneratorsOfGroup(GRPret)
  do
    for eMat in ListMat
    do
      if eGen*eMat*TransposedMat(eGen)<>eMat then
        Error("Error in ArithmeticAutomorphismMatrixFamily_HackSouvignier");
      fi;
    od;
  od;
  return GRPret;
end;

LattIsom_CreateAffineBasis:=function(SVR)
  local ListCanStart, i, eVect, n;
  n:=Length(SVR[1]);
  ListCanStart:=[];
  for i in [1..n]
  do
    eVect:=ListWithIdenticalEntries(n,0);
    eVect[i]:=1;
    if Position(SVR, eVect)<>fail then
      Add(ListCanStart, eVect);
    fi;
  od;
  return ExtendToCompleteAffineBasis(SVR, ListCanStart);
end;


ArithmeticAutomorphismMatrixFamily_HackSouvignier_V2:=function(TheOption, ListMat, SVR)
  local TheP;
  if IsPositiveDefiniteSymmetricMatrix(ListMat[1])=false then
    Error("The first matrix should be positive definite");
  fi;
  TheP:=LattIsom_CreateAffineBasis(SVR);
  return ArithmeticAutomorphismMatrixFamily_HackSouvignier(TheOption, ListMat, SVR, TheP);
end;



ArithmeticAutomorphismGroup:=function(ListGramMat)
  local InvariantBasis;
  InvariantBasis:=__ExtractInvariantZBasisShortVectorNoGroup(ListGramMat[1]);
  return ArithmeticAutomorphismMatrixFamily_HackSouvignier_V2("", ListGramMat, InvariantBasis);
end;



ArithmeticEquivalenceMatrixFamily_Souvignier:=function(TheOption, ListMat1, SVR1, ListMat2, SVR2)
  local n, n1, n2, FileIn, FileOut, FileGap, FileError32, FileError64, output, ChainOption, eMat, eVect, i, TheNorm, REP, KeyTest, TheReply, iMat, TheClean, rListMat1, rListMat2, TheMult, eRec, eLine, eEnt;
  n1:=Length(ListMat1[1]);
  n2:=Length(ListMat2[1]);
  if n1<>n2 then
    Error("It is not allowed to have two input matrices of different size");
  fi;
  n:=n1;
  if Length(SVR1)=0 and Length(SVR2) > 0 then
    Error("Either you provide basis as input for both or neither");
  fi;
  if Length(SVR2)=0 and Length(SVR1) > 0 then
    Error("Either you provide basis as input for both or neither");
  fi;
  if IsPositiveDefiniteSymmetricMatrix(ListMat1[1])=false then
    Error("The first matrix of ListMat1 should be positive definite");
  fi;
  if IsPositiveDefiniteSymmetricMatrix(ListMat2[1])=false then
    Error("The first matrix of ListMat2 should be positive definite");
  fi;
  TheMult:=1;
  for eMat in ListMat1
  do
    for eLine in eMat
    do
      for eEnt in eLine
      do
        TheMult:=LcmInt(TheMult, DenominatorRat(eEnt));
      od;
    od;
  od;
  for eMat in ListMat2
  do
    for eLine in eMat
    do
      for eEnt in eLine
      do
        TheMult:=LcmInt(TheMult, DenominatorRat(eEnt));
      od;
    od;
  od;
  rListMat1:=[];
  for eMat in ListMat1
  do
    Add(rListMat1, TheMult*eMat);
  od;
  rListMat2:=[];
  for eMat in ListMat2
  do
    Add(rListMat2, TheMult*eMat);
  od;
  TheClean:=function()
    RemoveFile(FileIn);
    RemoveFile(FileOut);
    RemoveFile(FileGap);
    RemoveFile(FileError32);
    RemoveFile(FileError64);
  end;
  FileIn:=Filename(POLYHEDRAL_tmpdir, "EQUIV.in");
  FileOut:=Filename(POLYHEDRAL_tmpdir, "EQUIV.out");
  FileGap:=Filename(POLYHEDRAL_tmpdir, "EQUIV.gap");
  FileError32:=Filename(POLYHEDRAL_tmpdir, "EQUIV.error32");
  FileError64:=Filename(POLYHEDRAL_tmpdir, "EQUIV.error64");
  output:=OutputTextFile(FileIn, true);
  AppendTo(output, "#", Length(ListMat1), "\n");
  for eMat in rListMat1
  do
    AUTO_ISOM__PrintMatrix(output, eMat);
  od;
  #
  KeyTest:=DoesItContainStandardBasis(SVR1) and DoesItContainStandardBasis(SVR2);
  ChainOption:="";
  if KeyTest=true then
    ChainOption:=" -V3";
    AppendTo(output, "\n");
    AppendTo(output, Length(SVR1), "\n");
    for eVect in SVR1
    do
      for i in [1..n]
      do
        AppendTo(output, " ", eVect[i]);
      od;
      TheNorm:=eVect*rListMat1[1]*eVect;
      AppendTo(output, " ", TheNorm, "\n");
    od;
  fi;
  for eMat in rListMat2
  do
    AUTO_ISOM__PrintMatrix(output, eMat);
  od;
  if KeyTest=true then
    AppendTo(output, "\n");
    AppendTo(output, Length(SVR2), "\n");
    for eVect in SVR2
    do
      for i in [1..n]
      do
        AppendTo(output, " ", eVect[i]);
      od;
      TheNorm:=eVect*rListMat2[1]*eVect;
      AppendTo(output, " ", TheNorm, "\n");
    od;
  fi;
  CloseStream(output);
  # not completely satisfying here ...
  Exec(FileISOM32, TheOption, ChainOption, " ", FileIn, " > ", FileOut, " 2>", FileError32);
  if IsEmptyFile(FileError32)=false then
    Print("Error at 32 bit arithmetic, trying 64 bits...\n");
    RemoveFile(FileOut);
    Exec(FileISOM64, TheOption, ChainOption, " ", FileIn, " > ", FileOut, " 2>", FileError64);
    if IsEmptyFile(FileError64)=false then
      Error("Error also at 64 bits in ArithmeticEquivalenceMatrixFamily_Souvignier");
    fi;
  fi;
  Exec(FileISOMtoGAP, " ", FileOut, " > ", FileGap);
  REP:=ReadAsFunction(FileGap)();
  if REP=false then
    TheClean();
    return false;
  fi;
  TheReply:=Inverse(REP);
  for iMat in [1..Length(ListMat1)]
  do
    if TheReply*ListMat1[iMat]*TransposedMat(TheReply)<>ListMat2[iMat] then
      Error("Error in ArithmeticEquivalenceMatrixFamily_Souvignier");
    fi;
  od;
  if Set(SVR1*Inverse(TheReply))<>Set(SVR2) then
    Print("The SVR1 / SVR2 are not mapped. This is a feature, not a bug.\n");
    Print("But likely not what you want.\n");
  fi;
  TheClean();
  return TheReply;
end;

ArithmeticEquivalenceMatrixFamily_HackSouvignier:=function(TheOption, ListMat1, SVR1, AffBas1, ListMat2, SVR2, AffBas2)
  local ListMat1mapped, SVR1mapped, ListMat2mapped, SVR2mapped, TheReplyMapped, TheReply, iMat;
  if IsPositiveDefiniteSymmetricMatrix(ListMat1[1])=false then
    Error("The first matrix of ListMat1 should be positive definite");
  fi;
  if IsPositiveDefiniteSymmetricMatrix(ListMat2[1])=false then
    Error("The first matrix of ListMat2 should be positive definite");
  fi;
  ListMat1mapped:=List(ListMat1, x->AffBas1*x*TransposedMat(AffBas1));
  if Length(SVR1)=0 then
    SVR1mapped:=[];
  else
    SVR1mapped:=SVR1*Inverse(AffBas1);
  fi;
  ListMat2mapped:=List(ListMat2, x->AffBas2*x*TransposedMat(AffBas2));
  if Length(SVR2)=0 then
    SVR2mapped:=[];
  else
    SVR2mapped:=SVR2*Inverse(AffBas2);
  fi;
  TheReplyMapped:=ArithmeticEquivalenceMatrixFamily_Souvignier(TheOption, ListMat1mapped, SVR1mapped, ListMat2mapped, SVR2mapped);
  if TheReplyMapped=false then
    return false;
  fi;
  TheReply:=Inverse(AffBas2)*TheReplyMapped*AffBas1;
  for iMat in [1..Length(ListMat1)]
  do
    if TheReply*ListMat1[iMat]*TransposedMat(TheReply)<>ListMat2[iMat] then
      Error("ArithmeticEquivalenceMatrixFamily_HackSouvignier: matrix inconsistency");
    fi;
  od;
  return TheReply;
end;





ArithmeticEquivalenceMatrixFamily_HackSouvignier_V2:=function(TheOption, ListMat1, SVR1, ListMat2, SVR2)
  local TheP1, TheP2;
  if IsPositiveDefiniteSymmetricMatrix(ListMat1[1])=false then
    Error("The first matrix of ListMat1 should be positive definite");
  fi;
  if IsPositiveDefiniteSymmetricMatrix(ListMat2[1])=false then
    Error("The first matrix of ListMat2 should be positive definite");
  fi;
  TheP1:=LattIsom_CreateAffineBasis(SVR1);
  TheP2:=LattIsom_CreateAffineBasis(SVR2);
  return ArithmeticEquivalenceMatrixFamily_HackSouvignier(TheOption, ListMat1, SVR1, TheP1, ListMat2, SVR2, TheP2);
end;






ArithmeticIsomorphism_Isom:=function(ListGramMat1, ListGramMat2)
  local InvariantBasis1, InvariantBasis2;
  InvariantBasis1:=__ExtractInvariantZBasisShortVectorNoGroup(ListGramMat1[1]);
  InvariantBasis2:=__ExtractInvariantZBasisShortVectorNoGroup(ListGramMat2[1]);
  return ArithmeticEquivalenceMatrixFamily_HackSouvignier_V2("", ListGramMat1, InvariantBasis1, ListGramMat2, InvariantBasis2);
end;

__CharacteristicGraphMatrixFamily:=function(ListMat, SVR)
  local nbV, DistMat, iVect, jVect, TheRec;
  nbV:=Length(SVR);
#  Print("nbV=", nbV, "\n");
#  Print("|ListMat|=", Length(ListMat), "\n");
  DistMat:=NullMat(nbV, nbV);
  for iVect in [1..nbV-1]
  do
    for jVect in [iVect+1..nbV]
    do
      TheRec:=List(ListMat, x->SVR[iVect]*x*SVR[jVect]);
      DistMat[iVect][jVect]:=TheRec;
      DistMat[jVect][iVect]:=TheRec;
    od;
  od;
  return DistMat;
end;


ArithmeticAutomorphismMatrixFamily_NautyCPP:=function(ListMat, SVR)
  local FileIn, FileOut, FileErr, nbMat, nbVect, n, output, iMat, eMat, i, j, iVect, GRP, TheCommand;
  FileIn:=Filename(POLYHEDRAL_tmpdir, "AutoNautyCpp.in");
  FileOut:=Filename(POLYHEDRAL_tmpdir, "AutoNautyCpp.out");
  FileErr:=Filename(POLYHEDRAL_tmpdir, "AutoNautyCpp.err");
  nbMat:=Length(ListMat);
  nbVect:=Length(SVR);
  n:=Length(SVR[1]);
  Print("nbMat=", nbMat, "\n");
  Print("nbVect=", nbVect, "\n");
  Print("n=", n, "\n");
  #
  output:=OutputTextFile(FileIn, true);
  AppendTo(output, nbMat, "\n");
  for iMat in [1..nbMat]
  do
    AppendTo(output, n, " ", n, "\n");
    eMat:=ListMat[iMat];
    for i in [1..n]
    do
      for j in [1..n]
      do
        AppendTo(output, " ", eMat[i][j]);
      od;
      AppendTo(output, "\n");
    od;
  od;
  AppendTo(output, nbVect, " ", n, "\n");
  for iVect in [1..nbVect]
  do
    for i in [1..n]
    do
      AppendTo(output, " ", SVR[iVect][i]);
    od;
    AppendTo(output, "\n");
  od;
  CloseStream(output);
  Print(NullMat(5));
  #
  TheCommand:=Concatenation(FileAutoVectorFamily, " ", FileIn, " ", FileOut, " > ", FileErr);
  Exec(TheCommand);
  #
  GRP:=ReadAsFunction(FileOut);
  RemoveFileIfExist(FileIn);
  RemoveFileIfExist(FileOut);
  RemoveFileIfExist(FileErr);
  return GRP;
end;


ArithmeticAutomorphismMatrixFamily_HackSouvignier_SVRmap:=function(TheOption, ListMat, SVR)
  local GRP, eGen;
  GRP:=ArithmeticAutomorphismMatrixFamily_HackSouvignier_V2(TheOption, ListMat, SVR);
  for eGen in GeneratorsOfGroup(GRP)
  do
    if Set(SVR*eGen)<>Set(SVR) then
      return ArithmeticAutomorphismMatrixFamily_NautyCPP(ListMat, SVR);
    fi;
  od;
  return GRP;
end;


ArithmeticAutomorphismMatrixFamily_Nauty_Scalable:=function(ListMat, SVR)
  local GetScalarColor, GetLineColor, eRecScalColor;
  GetScalarColor:=function(i,j)
    return List(ListMat, x->SVR[i]*x*SVR[j]);
  end;
  GetLineColor:=function(i)
    local ListV;
    ListV:=List(ListMat, x->SVR[i]*x);
    return List(SVR, x->List(ListV, y->y*x));
  end;
  eRecScalColor:=rec(n:=Length(SVR),
                     GetScalarColor:=GetScalarColor,
                     GetLineColor:=GetLineColor);
  return AutomorphismGroupColoredGraph_Scalable(eRecScalColor);
end;




ArithmeticAutomorphismMatrixFamily_Nauty:=function(ListMat, SVR)
  local DistMat, GRP, ListMatGens, eGen, MatrixGRP, eMat;
  if Length(SVR)<>Length(Set(SVR)) then
    Error("Unauthorized repetitiont in characteristic set");
  fi;
  if RankMat(SVR)<>Length(ListMat[1][1]) then
    Error("Wrong SVR argument");
  fi;
  DistMat:=__CharacteristicGraphMatrixFamily(ListMat, SVR);
  GRP:=AutomorphismGroupEdgeColoredGraph(DistMat);
  ListMatGens:=List(GeneratorsOfGroup(GRP), x->FindTransformation(SVR, SVR, x));
  MatrixGRP:=Group(ListMatGens);
  SetSize(MatrixGRP, Order(GRP));
  for eGen in GeneratorsOfGroup(MatrixGRP)
  do
    if IsIntegralMat(eGen)=false then
      Print("Generator eGen is not integral\n");
      Print("DeterminantMat(BaseIntMat(SVR))=", DeterminantMat(BaseIntMat(SVR)), "\n");
      Print("It is likely because SVR is not generating\n");
      Print("Otherwise, please search\n");
      Error("Please correct");
    fi;
    for eMat in ListMat
    do
      if eGen*eMat*TransposedMat(eGen)<>eMat then
        Error("Error in ArithmeticAutomorphismMatrixFamily_Nauty");
      fi;
    od;
  od;
  return MatrixGRP;
end;


ArithmeticAutomorphismSymmetricAntisymmetric:=function(ListSym, ListAntisym)
  local SVR, ListMat, nbVect, TheMat, iVect, eLine, jVect, LScal, PermGRP, ListMatGens, MatrixGRP, eGen, eMat;
  SVR:=__ExtractInvariantZBasisShortVectorNoGroup(ListSym[1]);
  ListMat:=Concatenation(ListSym, ListAntisym);
  nbVect:=Length(SVR);
  TheMat:=[];
  for iVect in [1..nbVect]
  do
    eLine:=[];
    for jVect in [1..nbVect]
    do
      LScal:=List(ListMat, x->SVR[iVect]*x*SVR[jVect]);
      Add(eLine, LScal);
    od;
    Add(TheMat, eLine);
  od;
  PermGRP:=AutomorphismWeightedDigraph(TheMat);
  ListMatGens:=List(GeneratorsOfGroup(PermGRP), x->FindTransformation(SVR, SVR, x));
  MatrixGRP:=Group(ListMatGens);
  SetSize(MatrixGRP, Order(PermGRP));
  for eGen in GeneratorsOfGroup(MatrixGRP)
  do
    for eMat in ListMat
    do
      if eGen*eMat*TransposedMat(eGen)<>eMat then
        Error("Error in ArithmeticAutomorphismMatrixFamily_Nauty");
      fi;
    od;
  od;
  return MatrixGRP;
end;


ArithmeticEquivalenceMatrixFamily_Nauty:=function(ListMat1, SVR1, ListMat2, SVR2)
  local DistMat1, DistMat2, eList, RetMat, iMat, RetMat2;
  if RankMat(SVR1)<>Length(ListMat1[1][1]) then
    Error("Wrong SVR1 argument");
  fi;
  if RankMat(SVR2)<>Length(ListMat2[1][1]) then
    Error("Wrong SVR2 argument");
  fi;
  DistMat1:=__CharacteristicGraphMatrixFamily(ListMat1, SVR1);
  DistMat2:=__CharacteristicGraphMatrixFamily(ListMat2, SVR2);
  eList:=IsIsomorphicEdgeColoredGraph(DistMat1, DistMat2);
  if eList=false then
    return false;
  fi;
  RetMat:=FindTransformation(SVR1, SVR2, PermList(eList));
  RetMat2:=Inverse(RetMat);
  for iMat in [1..Length(ListMat1)]
  do
    if RetMat2*ListMat1[iMat]*TransposedMat(RetMat2)<>ListMat2[iMat] then
      Error("Error in ArithmeticEquivalenceMatrixFamily_Nauty");
    fi;
  od;
  return RetMat2;
end;



ArithmeticEquivalenceMatrixFamily_HackSouvignier_SVRmap:=function(TheOption, ListMat1, SVR1, ListMat2, SVR2)
  local TheEquiv;
  TheEquiv:=ArithmeticEquivalenceMatrixFamily_HackSouvignier_V2(TheOption, ListMat1, SVR1, ListMat2, SVR2);
  if TheEquiv=false then
    return false;
  fi;
  if Set(SVR1*Inverse(TheEquiv))=Set(SVR2) then
    return TheEquiv;
  fi;
  return ArithmeticEquivalenceMatrixFamily_Nauty(ListMat1, SVR1, ListMat2, SVR2);
end;







ArithmeticIsomorphism_Nauty:=function(ListGramMat1, ListGramMat2)
  local InvariantBasis1, InvariantBasis2;
  InvariantBasis1:=__ExtractInvariantZBasisShortVectorNoGroup(ListGramMat1[1]);
  InvariantBasis2:=__ExtractInvariantZBasisShortVectorNoGroup(ListGramMat2[1]);
  return ArithmeticEquivalenceMatrixFamily_Nauty(ListGramMat1, InvariantBasis1, ListGramMat2, InvariantBasis2);
end;

GetReductionMatrix:=function(eGram)
  local n, NSP, eCompl, RedMat;
  n:=Length(eGram);
  NSP:=NullspaceIntMat(RemoveFractionMatrix(eGram));
  eCompl:=SubspaceCompletion(NSP, n);
  RedMat:=Concatenation(eCompl, NSP);
  return rec(rank:=Length(eCompl), RedMat:=RedMat);
end;


ArithmeticIsomorphismSemidefinite:=function(ListGram1, ListGram2)
  local eGram1, eGram2, eRed1, eRed2, rnk, Fred, ListGram1_Map, ListGram2_Map, eIsom, eIsomBig, i, j, eIsomRet, idx;
  eGram1:=Sum(ListGram1);
  eGram2:=Sum(ListGram2);
  eRed1:=GetReductionMatrix(eGram1);
  eRed2:=GetReductionMatrix(eGram2);
  if Length(ListGram1)<>Length(ListGram2) then
    return false;
  fi;
  if eRed1.rank<>eRed2.rank then
    return false;
  fi;
  rnk:=eRed1.rank;
  Fred:=function(Amat)
    return List(Amat{[1..rnk]}, x->x{[1..rnk]});
  end;
  ListGram1_Map:=List(ListGram1, x-> Fred(eRed1.RedMat * x * TransposedMat(eRed1.RedMat)));
  ListGram2_Map:=List(ListGram2, x-> Fred(eRed2.RedMat * x * TransposedMat(eRed2.RedMat)));
  eIsom:=ArithmeticIsomorphism_Nauty(ListGram1_Map, ListGram2_Map);
  if eIsom=false then
    return false;
  fi;
  eIsomBig:=IdentityMat(Length(eGram1));
  for i in [1..rnk]
  do
    for j in [1..rnk]
    do
      eIsomBig[i][j]:=eIsom[i][j];
    od;
  od;
  eIsomRet:=Inverse(eRed2.RedMat) * eIsomBig * eRed1.RedMat;
  for idx in [1..Length(ListGram1)]
  do
    if eIsomRet * ListGram1[idx] * TransposedMat(eIsomRet) <> ListGram2[idx] then
      Error("Consistency error in ListGram1 / ListGram2");
    fi;
  od;
  return eIsomRet;
end;



ArithmeticIsomorphism:=function(ListGramMat1, ListGramMat2)
  if Length(ListGramMat1)<>Length(ListGramMat2) then
    return false;
  fi;
  if IsPositiveDefiniteSymmetricMatrix(ListGramMat1[1])=false then
    return false;
  fi;
  if IsPositiveDefiniteSymmetricMatrix(ListGramMat2[1])=false then
    return false;
  fi;
  return ArithmeticIsomorphism_Isom(ListGramMat1, ListGramMat2);
#  return ArithmeticIsomorphism_Nauty(ListGramMat1, ListGramMat2);
end;





#ArithmeticAutomorphismMatrixFamily_Hack:=function(ListMat, SVR, AffBas)
#  return ArithmeticAutomorphismMatrixFamily_HackSouvignier(ListMat, SVR, AffBas);
##  return ArithmeticAutomorphismMatrixFamily_Nauty(ListMat, SVR);
#end;

#ArithmeticEquivalenceMatrixFamily_Hack:=function(ListMat1, SVR1, AffBas1, ListMat2, SVR2, AffBas2)
#  return ArithmeticEquivalenceMatrixFamily_HackSouvignier(ListMat1, SVR1, AffBas1, ListMat2, SVR2, AffBas2);
##  return ArithmeticEquivalenceMatrixFamily_Nauty(ListMat1, SVR1, ListMat2, SVR2);
#end;


#
#
# return the a generator of the group of matrices U
# satisfying to
# U*F*TransposedMat(U)=F
# We do a LLL reduction prior to it.
# unsure program and unsure to be faster.
MatrixAutomorphismGroupGramMatrix:=function(GramMat)
  return ArithmeticAutomorphismGroup([GramMat]);
end;


GetCompleteListGroups:=function()
  return [
rec(nb:=1, str:="P1"),
rec(nb:=2, str:="P-1"),
rec(nb:=3, str:="P2"),
rec(nb:=4, str:="P21"),
rec(nb:=5, str:="C2"),
rec(nb:=6, str:="Pm"),
rec(nb:=7, str:="Pc"),
rec(nb:=8, str:="Cm"),
rec(nb:=9, str:="Cc"),
rec(nb:=10, str:="P2/m"),
rec(nb:=10, str:="P12/m1"),
rec(nb:=11, str:="P21/m"),
rec(nb:=11, str:="P121/m1"),
rec(nb:=12, str:="C2/m"),
rec(nb:=13, str:="P2/c"),
rec(nb:=14, str:="P21/c"),
rec(nb:=15, str:="C2/c"),
rec(nb:=16, str:="P222"),
rec(nb:=17, str:="P2221"),
rec(nb:=18, str:="P21212"),
rec(nb:=19, str:="P212121"),
rec(nb:=20, str:="C2221"),
rec(nb:=21, str:="C222"),
rec(nb:=22, str:="F222"),
rec(nb:=23, str:="I222"),
rec(nb:=24, str:="I212121"),
rec(nb:=25, str:="Pmm2"),
rec(nb:=26, str:="Pmc21"),
rec(nb:=27, str:="Pcc2"),
rec(nb:=28, str:="Pma2"),
rec(nb:=29, str:="Pca21"),
rec(nb:=30, str:="Pnc2"),
rec(nb:=31, str:="Pmn21"),
rec(nb:=32, str:="Pba2"),
rec(nb:=33, str:="Pna21"),
rec(nb:=34, str:="Pnn2"),
rec(nb:=35, str:="Cmm2"),
rec(nb:=36, str:="Cmc21"),
rec(nb:=37, str:="Ccc2"),
rec(nb:=38, str:="Amm2"),
rec(nb:=39, str:="Aem2"),
rec(nb:=40, str:="Ama2"),
rec(nb:=41, str:="Aea2"),
rec(nb:=42, str:="Fmm2"),
rec(nb:=43, str:="Fdd2"),
rec(nb:=44, str:="Imm2"),
rec(nb:=45, str:="Iba2"),
rec(nb:=46, str:="Ima2"),
rec(nb:=47, str:="Pmmm"),
rec(nb:=48, str:="Pnnn"),
rec(nb:=49, str:="Pccm"),
rec(nb:=50, str:="Pban"),
rec(nb:=51, str:="Pmma"),
rec(nb:=52, str:="Pnna"),
rec(nb:=53, str:="Pmna"),
rec(nb:=54, str:="Pcca"),
rec(nb:=55, str:="Pbam"),
rec(nb:=56, str:="Pccn"),
rec(nb:=57, str:="Pbcm"),
rec(nb:=58, str:="Pnnm"),
rec(nb:=59, str:="Pmmn"),
rec(nb:=60, str:="Pbcn"),
rec(nb:=61, str:="Pbca"),
rec(nb:=62, str:="Pnma"),
rec(nb:=63, str:="Cmcm"),
rec(nb:=64, str:="Cmce"),
rec(nb:=64, str:="Cmca"),
rec(nb:=65, str:="Cmmm"),
rec(nb:=66, str:="Cccm"),
rec(nb:=67, str:="Cmme"),
rec(nb:=67, str:="Cmma"),
rec(nb:=68, str:="Ccce"),
rec(nb:=69, str:="Fmmm"),
rec(nb:=70, str:="Fddd"),
rec(nb:=71, str:="Immm"),
rec(nb:=72, str:="Ibam"),
rec(nb:=73, str:="Ibca"),
rec(nb:=74, str:="Imma"),
rec(nb:=75, str:="P4"),
rec(nb:=76, str:="P41"),
rec(nb:=77, str:="P42"),
rec(nb:=78, str:="P43"),
rec(nb:=79, str:="I4"),
rec(nb:=80, str:="I41"),
rec(nb:=81, str:="P-4"),
rec(nb:=82, str:="I-4"),
rec(nb:=83, str:="P4/m"),
rec(nb:=84, str:="P42/m"),
rec(nb:=85, str:="P4/n"),
rec(nb:=86, str:="P42/n"),
rec(nb:=87, str:="I4/m"),
rec(nb:=88, str:="I41/a"),
rec(nb:=89, str:="P422"),
rec(nb:=90, str:="P4212"),
rec(nb:=91, str:="P4122"),
rec(nb:=92, str:="P41212"),
rec(nb:=93, str:="P4222"),
rec(nb:=94, str:="P42212"),
rec(nb:=95, str:="P4322"),
rec(nb:=96, str:="P43212"),
rec(nb:=97, str:="I422"),
rec(nb:=98, str:="I4122"),
rec(nb:=99, str:="P4mm"),
rec(nb:=100, str:="P4bm"),
rec(nb:=101, str:="P42cm"),
rec(nb:=102, str:="P42nm"),
rec(nb:=103, str:="P4cc"),
rec(nb:=104, str:="P4nc"),
rec(nb:=105, str:="P42mc"),
rec(nb:=106, str:="P42bc"),
rec(nb:=107, str:="I4mm"),
rec(nb:=108, str:="I4cm"),
rec(nb:=109, str:="I41md"),
rec(nb:=110, str:="I41cd"),
rec(nb:=111, str:="P-42m"),
rec(nb:=112, str:="P-42c"),
rec(nb:=113, str:="P-421m"),
rec(nb:=114, str:="P-421c"),
rec(nb:=115, str:="P-4m2"),
rec(nb:=116, str:="P-4c2"),
rec(nb:=117, str:="P-4b2"),
rec(nb:=118, str:="P-4n2"),
rec(nb:=119, str:="I-4m2"),
rec(nb:=120, str:="I-4c2"),
rec(nb:=121, str:="I-42m"),
rec(nb:=122, str:="I-42d"),
rec(nb:=123, str:="P4/mmm"),
rec(nb:=124, str:="P4/mcc"),
rec(nb:=125, str:="P4/nbm"),
rec(nb:=126, str:="P4/nnc"),
rec(nb:=127, str:="P4/mbm"),
rec(nb:=128, str:="P4/mnc"),
rec(nb:=129, str:="P4/nmm"),
rec(nb:=130, str:="P4/ncc"),
rec(nb:=131, str:="P42/mmc"),
rec(nb:=132, str:="P42/mcm"),
rec(nb:=133, str:="P42/nbc"),
rec(nb:=134, str:="P42/nnm"),
rec(nb:=135, str:="P42/mbc"),
rec(nb:=136, str:="P42/mnm"),
rec(nb:=137, str:="P42/nmc"),
rec(nb:=138, str:="P42/ncm"),
rec(nb:=139, str:="I4/mmm"),
rec(nb:=140, str:="I4/mcm"),
rec(nb:=141, str:="I41/amd"),
rec(nb:=142, str:="I41/acd"),
rec(nb:=143, str:="P3"),
rec(nb:=144, str:="P31"),
rec(nb:=145, str:="P32"),
rec(nb:=146, str:="R3"),
rec(nb:=147, str:="P-3"),
rec(nb:=148, str:="R-3"),
rec(nb:=149, str:="P312"),
rec(nb:=150, str:="P321"),
rec(nb:=151, str:="P3112"),
rec(nb:=152, str:="P3121"),
rec(nb:=153, str:="P3212"),
rec(nb:=154, str:="P3221"),
rec(nb:=155, str:="R32"),
rec(nb:=156, str:="P3m1"),
rec(nb:=157, str:="P31m"),
rec(nb:=158, str:="P3c1"),
rec(nb:=159, str:="P31c"),
rec(nb:=160, str:="R3m"),
rec(nb:=161, str:="R3c"),
rec(nb:=162, str:="P-31m"),
rec(nb:=163, str:="P-31c"),
rec(nb:=164, str:="P-3m1"),
rec(nb:=165, str:="P-3c1"),
rec(nb:=166, str:="R-3m"),
rec(nb:=167, str:="R-3c"),
rec(nb:=168, str:="P6"),
rec(nb:=169, str:="P61"),
rec(nb:=170, str:="P65"),
rec(nb:=171, str:="P62"),
rec(nb:=172, str:="P64"),
rec(nb:=173, str:="P63"),
rec(nb:=174, str:="P-6"),
rec(nb:=175, str:="P6/m"),
rec(nb:=176, str:="P63/m"),
rec(nb:=177, str:="P622"),
rec(nb:=178, str:="P6122"),
rec(nb:=179, str:="P6522"),
rec(nb:=180, str:="P6222"),
rec(nb:=181, str:="P6422"),
rec(nb:=182, str:="P6322"),
rec(nb:=183, str:="P6mm"),
rec(nb:=184, str:="P6cc"),
rec(nb:=185, str:="P63cm"),
rec(nb:=186, str:="P63mc"),
rec(nb:=187, str:="P-6m2"),
rec(nb:=188, str:="P-6c2"),
rec(nb:=189, str:="P-62m"),
rec(nb:=190, str:="P-62c"),
rec(nb:=191, str:="P6/mmm"),
rec(nb:=192, str:="P6/mcc"),
rec(nb:=193, str:="P63/mcm"),
rec(nb:=194, str:="P63/mmc"),
rec(nb:=195, str:="P23"),
rec(nb:=196, str:="F23"),
rec(nb:=197, str:="I23"),
rec(nb:=198, str:="P213"),
rec(nb:=199, str:="I213"),
rec(nb:=200, str:="Pm-3"),
rec(nb:=201, str:="Pn-3"),
rec(nb:=202, str:="Fm-3"),
rec(nb:=203, str:="Fd-3"),
rec(nb:=204, str:="Im-3"),
rec(nb:=205, str:="Pa-3"),
rec(nb:=206, str:="Ia-3"),
rec(nb:=207, str:="P432"),
rec(nb:=208, str:="P4232"),
rec(nb:=209, str:="F432"),
rec(nb:=210, str:="F4132"),
rec(nb:=211, str:="I432"),
rec(nb:=212, str:="P4332"),
rec(nb:=213, str:="P4132"),
rec(nb:=214, str:="I4132"),
rec(nb:=215, str:="P-43m"),
rec(nb:=216, str:="F-43m"),
rec(nb:=217, str:="I-43m"),
rec(nb:=218, str:="P-43n"),
rec(nb:=219, str:="F-43c"),
rec(nb:=220, str:="I-43d"),
rec(nb:=221, str:="Pm-3m"),
rec(nb:=222, str:="Pn-3n"),
rec(nb:=223, str:="Pm-3n"),
rec(nb:=224, str:="Pn-3m"),
rec(nb:=225, str:="Fm-3m"),
rec(nb:=226, str:="Fm-3c"),
rec(nb:=227, str:="Fd-3m"),
rec(nb:=228, str:="Fd-3c"),
  rec(nb:=229, str:="Im-3m"),
  rec(nb:=230, str:="Ia-3d")];
end;

Find3dimensionalSymmetry:=function(TheMatrGRP)
  local ListBigGens, nbGen, n, PtGroup, NewListBigGens, i, eVect, eGen, SpaceGrp, MainPt, MainOrd, S2, PGrp, OrdSpc, iso, res, TheDet, ListReturn, eEnt, TheListTotal, FuncReduction, FuncCreateBigMatCrystType, eBigGen, eRec, eNGen;
  ListBigGens:=GeneratorsOfGroup(TheMatrGRP);
  nbGen:=Length(ListBigGens);
  n:=Length(ListBigGens[1])-1;
  if n > 3 then
    Error("The program works only for dimension 3 and possibly 2");
  fi;
  FuncCreateBigMatCrystType:=function(eTrans, eMat)
    local Umat, i, j;
    Umat:=NullMat(n+1,n+1);
    for i in [1..n]
    do
      for j in [1..n]
      do
        Umat[i][j]:=eMat[i][j];
      od;
    od;
    for i in [1..n]
    do
      Umat[n+1][i]:=eTrans[i];
    od;
    Umat[n+1][n+1]:=1;
    return Umat;
  end;
  FuncReduction:=function(eBigMat)
    return List(eBigMat{[1..n]}, x->x{[1..n]});
  end;
  PtGroup:=function(SPG)
    local U, U2;
    U:=GeneratorsOfGroup(SPG);
    U2:=List(U, FuncReduction);
    return Group(U2);
  end;
  NewListBigGens:=[];
  for i in [1..n]
  do
    eVect:=ListWithIdenticalEntries(n,0);
    eVect[i]:=1;
    eGen:=FuncCreateBigMatCrystType(eVect, IdentityMat(n));
    Add(NewListBigGens, eGen);
  od;
  for eBigGen in ListBigGens
  do
    eRec:=FuncExplodeBigMatrix(eBigGen);
    eNGen:=FuncCreateBigMatCrystType(eRec.eTrans, eRec.MatrixTransformation);
    Add(NewListBigGens, eNGen);
  od;
  SpaceGrp:=AffineCrystGroupOnRight(NewListBigGens);
  MainPt:=PtGroup(SpaceGrp);
  MainOrd:=Order(MainPt);
  if n=3 then
    for i in [1..230]
    do
      S2:=SpaceGroupOnRightIT(3, i);
      PGrp:=PtGroup(S2);
      OrdSpc:=Order(PGrp);
      if OrdSpc=MainOrd then
        iso:=IsomorphismGroups(PGrp, MainPt);
        if iso<>fail then
          res:=ConjugatorSpaceGroups(SpaceGrp, S2);
          if res<>fail then
            TheDet:=DeterminantMat(res);
            TheListTotal:=GetCompleteListGroups();
            ListReturn:=[];
            for eEnt in TheListTotal
            do
              if eEnt.nb=i then
                Add(ListReturn, eEnt.str);
              fi;
            od;
            return ListReturn;
          fi;
        fi;
      fi;
    od;
    Error("We should not reach that stage");
  fi;
end;
