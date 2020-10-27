FileGraysonDiagram:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"GraysonDiagram");
# returns the Hermite constant at the n-th power.
# that is the minimum of min(A)^n/det(A).
GetHermitePower:=function(n)
  local h;
  if n=1 then
    return 1;
  fi;
  if n=2 then
    return 4/3;
  fi;
  if n=3 then
    return 2;
  fi;
  if n=4 then
    return 4;
  fi;
  if n=5 then
    return 8;
  fi;
  if n=6 then
    return 64/3;
  fi;
  if n=7 then
    return 64;
  fi;
  if n=8 then
    return 256;
  fi;
  h:=n*(n-1)/2;
  return (4/3)^h;
end;


IsEquivalentRepresentationSublattice:=function(eLatt, fLatt)
  local eVect, eSol;
  for eVect in eLatt
  do
    eSol:=SolutionIntMat(fLatt, eVect);
    if eSol=fail then
      return false;
    fi;
  od;
  return true;
end;


GetStabilizerSublattice_V1:=function(TheGramMat, SHVbig, eRecLatt)
  local SetSHVbig, SHV, SVR, nb, DistMat, i, j, eScal, eVect, pos, GRPperm, ListMatGens, ePermGen, eMatrGen, MatrixGRP, eImgLatt;
  SetSHVbig:=Set(SHVbig);
  SHV:=eRecLatt.SHV*eRecLatt.TheLattice;
  SVR:=Union(SetSHVbig, Set(SHV));
  nb:=Length(SVR);
  DistMat:=NullMat(nb+1, nb+1);
  for i in [1..nb]
  do
    for j in [1..nb]
    do
      eScal:=SVR[i]*TheGramMat*SVR[j];
      DistMat[i][j]:=eScal;
    od;
  od;
  for eVect in SHV
  do
    pos:=Position(SVR, eVect);
    DistMat[pos][nb+1]:=1;
    DistMat[nb+1][pos]:=1;
  od;
  DistMat[nb+1][nb+1]:=-1;
  GRPperm:=AutomorphismGroupColoredGraph(DistMat);
  ListMatGens:=[];
  for ePermGen in GeneratorsOfGroup(GRPperm)
  do
    eMatrGen:=FindTransformation(SVR, SVR, ePermGen);
    if IsIntegralMat(eMatrGen)=false then
      Error("The matrix should be integral");
    fi;
    if eMatrGen*TheGramMat*TransposedMat(eMatrGen) <> TheGramMat then
      Error("eMatrGen does not preserve the gram matrix");
    fi;
    eImgLatt:=eRecLatt.TheLattice*eMatrGen;
    if IsEquivalentRepresentationSublattice(eImgLatt, eRecLatt.TheLattice)=false then
      Error("We should have an equivalence here");
    fi;
    Add(ListMatGens, eMatrGen);
  od;
  MatrixGRP:=Group(ListMatGens);
  SetSize(MatrixGRP, Order(GRPperm));
  return MatrixGRP;
end;


# orthogonal projector means self adjoint.
# that is that we have
# <x, p(y)> = < p(x), y>
# We have the scalar product <x,y> = X G Y^t
# and so we get
# <p(x), y> = XP G Y^T
# <x, p(y)> = XG P^T Y
# so we have PG = G P^T
__GetOrthogonalProjector:=function(TheGramMat, TheSubBasis)
  local hDim, eGram, eGramInv, TheProj, fVect, Bside, eSol, xProj, j, n, eDiff;
  n:=Length(TheGramMat);
  hDim:=Length(TheSubBasis);
  eGram:=TheSubBasis*TheGramMat*TransposedMat(TheSubBasis);
  eGramInv:=Inverse(eGram);
  TheProj:=[];
  for fVect in IdentityMat(n)
  do
    Bside:=List(TheSubBasis, x->x*TheGramMat*fVect);
    eSol:=Bside*eGramInv;
    xProj:=ListWithIdenticalEntries(n,0);
    for j in [1..hDim]
    do
      xProj:=xProj + eSol[j]*TheSubBasis[j];
    od;
    Add(TheProj, xProj);
  od;
  eDiff:=TheProj*TheGramMat - TheGramMat*TransposedMat(TheProj);
  if eDiff<>NullMat(n,n) then
    Error("Projector matrix is not symmetric");
  fi;
  return TheProj;
end;





GetPairForSublattice:=function(TheGramMat, SHVbig, eRecLatt)
  local SetSHVbig, eMult, SHV, SVR, TheProj, RedMat;
  SetSHVbig:=Set(SHVbig);
  eMult:=1;
  while(true)
  do
    SHV:=eMult * eRecLatt.SHV*eRecLatt.TheLattice;
    if Length(Intersection(SetSHVbig, Set(SHV)))=0 then
      break;
    fi;
    eMult:=eMult+1;
  od;
  SVR:=Union(SetSHVbig, Set(SHV));
  #
  # building the projector matrix
  #
  TheProj:=__GetOrthogonalProjector(TheGramMat, eRecLatt.TheLattice);
  RedMat:=TheProj*TheGramMat*TransposedMat(TheProj);
  return rec(SVR:=SVR, RedMat:=RedMat, TheProj:=TheProj);
end;


GetStabilizerSublattice_V2:=function(TheGramMat, SHVbig, eRecLatt)
  local RecProj, eVect, ListMatGens, eMatrGen, eImgLatt, GRPmat;
  RecProj:=GetPairForSublattice(TheGramMat, SHVbig, eRecLatt);
  #
#  GRPmat:=ArithmeticAutomorphismMatrixFamily_HackSouvignier_SVRmap("", [TheGramMat, RedMat], SVR);
  GRPmat:=ArithmeticAutomorphismMatrixFamily_Nauty([TheGramMat, RecProj.RedMat], RecProj.SVR);
  ListMatGens:=GeneratorsOfGroup(GRPmat);
  for eMatrGen in ListMatGens
  do
    if IsIntegralMat(eMatrGen)=false then
      Error("The matrix should be integral");
    fi;
    if eMatrGen*TheGramMat*TransposedMat(eMatrGen) <> TheGramMat then
      Error("eMatrGen does not preserve the gram matrix");
    fi;
    eImgLatt:=eRecLatt.TheLattice*eMatrGen;
    if IsEquivalentRepresentationSublattice(eImgLatt, eRecLatt.TheLattice)=false then
      Error("We have an inconsistency in equivalences");
    fi;
  od;
  return GRPmat;
end;



GetInvariantSublattice:=function(TheGramMat, SHVbig, eRecLatt)
  local RecProj, lenSVR, ScalarMat, ListMat, eV, eLine, fV, eLscal;
  RecProj:=GetPairForSublattice(TheGramMat, SHVbig, eRecLatt);
  lenSVR:=Length(RecProj.SVR);
  ScalarMat:=[];
  ListMat:=[TheGramMat, RecProj.RedMat];
  for eV in RecProj.SVR
  do
    eLine:=[];
    for fV in RecProj.SVR
    do
      eLscal:=List(ListMat, x->eV*x*fV);
      Add(eLine, eLscal);
    od;
    Add(ScalarMat, eLine);
  od;
  return DistMat_Invariant(ScalarMat);
end;



GetStabilizerSublattice:=GetStabilizerSublattice_V1;
#GetStabilizerSublattice:=GetStabilizerSublattice_V2;



TestEquivalenceSublattice_V1:=function(TheGramMat, SHVbig, eRecLatt1, eRecLatt2)
  local SetSHVbig, SHV1, SHV2, SVR1, SVR2, nb, DistMat1, DistMat2, i, j, eScal1, eScal2, eVect, pos, eList, RetMat, eImgLatt;
  if Length(eRecLatt1.SHV)<>Length(eRecLatt2.SHV) or eRecLatt1.TheDet<>eRecLatt2.TheDet then
    return false;
  fi;
  SetSHVbig:=Set(SHVbig);
  SHV1:=eRecLatt1.SHV*eRecLatt1.TheLattice;
  SHV2:=eRecLatt2.SHV*eRecLatt2.TheLattice;
  SVR1:=Union(SetSHVbig, Set(SHV1));
  SVR2:=Union(SetSHVbig, Set(SHV2));
  Print("|SVR1|=", Length(SVR1), " |SVR2|=", Length(SVR2), "\n");
  if Length(SVR1)<>Length(SVR2) then
    return false;
  fi;
  nb:=Length(SVR1);
  DistMat1:=NullMat(nb+1, nb+1);
  DistMat2:=NullMat(nb+1, nb+1);
  for i in [1..nb]
  do
    for j in [1..nb]
    do
      eScal1:=SVR1[i]*TheGramMat*SVR1[j];
      eScal2:=SVR2[i]*TheGramMat*SVR2[j];
      DistMat1[i][j]:=eScal1;
      DistMat2[i][j]:=eScal2;
    od;
  od;
  for eVect in SHV1
  do
    pos:=Position(SVR1, eVect);
    DistMat1[pos][nb+1]:=1;
    DistMat1[nb+1][pos]:=1;
  od;
  for eVect in SHV2
  do
    pos:=Position(SVR2, eVect);
    DistMat2[pos][nb+1]:=1;
    DistMat2[nb+1][pos]:=1;
  od;
  DistMat1[nb+1][nb+1]:=-1;
  DistMat2[nb+1][nb+1]:=-1;
  eList:=IsIsomorphicColoredGraph(DistMat1, DistMat2);
  if eList=false then
    return false;
  fi;
  RetMat:=FindTransformation(SVR1, SVR2, PermList(eList));
  if IsIntegralMat(RetMat)=false then
    Error("The matrix should be integral");
  fi;
  eImgLatt:=eRecLatt1.TheLattice*RetMat;
  if IsEquivalentRepresentationSublattice(eImgLatt, eRecLatt2.TheLattice)=false then
    Error("We have an inconsistency in TestEquivalenceSublattice_V1");
  fi;
  return RetMat;
end;



TestEquivalenceSublattice_V2:=function(TheGramMat, SHVbig, eRecLatt1, eRecLatt2)
  local SetSHVbig, SHV1, SHV2, SVR1, SVR2, nb, DistMat1, DistMat2, i, j, eScal1, eScal2, eVect, pos, eList, RetMat, eImgLatt, TheProj1, TheProj2, RedMat1, RedMat2, preRetMat, eMult;
#  Print("|eRecLatt1.SHV|=", Length(eRecLatt1.SHV), " |eRecLatt2.SHV|=", Length(eRecLatt2.SHV), "\n");
  if Length(eRecLatt1.SHV)<>Length(eRecLatt2.SHV) then
    return false;
  fi;
  if eRecLatt1.TheDet<>eRecLatt2.TheDet then
    return false;
  fi;
  if Length(eRecLatt1.TheLattice)<>Length(eRecLatt2.TheLattice) then
    return false;
  fi;
  SetSHVbig:=Set(SHVbig);
  eMult:=1;
  while(true)
  do
    SHV1:=Set(eMult * eRecLatt1.SHV*eRecLatt1.TheLattice);
    SHV2:=Set(eMult * eRecLatt2.SHV*eRecLatt2.TheLattice);
    if Length(Intersection(SetSHVbig, SHV1))=0 and Length(Intersection(SetSHVbig, SHV2))=0 then
      break;
    fi;
    eMult:=eMult+1;
  od;
  SVR1:=Union(SetSHVbig, SHV1);
  SVR2:=Union(SetSHVbig, SHV2);
  if Length(SVR1)<>Length(SVR2) then
    return false;
  fi;
  TheProj1:=__GetOrthogonalProjector(TheGramMat, eRecLatt1.TheLattice);
  TheProj2:=__GetOrthogonalProjector(TheGramMat, eRecLatt2.TheLattice);
  RedMat1:=TheProj1*TheGramMat*TransposedMat(TheProj1);
  RedMat2:=TheProj2*TheGramMat*TransposedMat(TheProj1);
#  preRetMat:=ArithmeticEquivalenceMatrixFamily_HackSouvignier_SVRmap("", Concatenation(ListGramMat, [RedMat1]), SVR1, Concatenation(ListGramMat, [RedMat2]), SVR2);
  preRetMat:=ArithmeticEquivalenceMatrixFamily_Nauty([TheGramMat, RedMat1], SVR1, [TheGramMat, RedMat2], SVR2);
  if preRetMat=false then
    return false;
  fi;
  RetMat:=Inverse(preRetMat);
  if IsIntegralMat(RetMat)=false then
    Error("The matrix should be integral");
  fi;
  if Set(SHV1*RetMat)<>Set(SHV2) then
    Error("The sets SHV1 / SHV2 should be mapped");
  fi;
  if Set(SVR1*RetMat)<>Set(SVR2) then
    Error("The sets SVR1 / SVR2 should be mapped");
  fi;
  eImgLatt:=eRecLatt1.TheLattice*RetMat;
  if IsEquivalentRepresentationSublattice(eImgLatt, eRecLatt2.TheLattice)=false then
    Error("We have an inconsistency in TestEquivalenceSublattice_V2");
  fi;
  return RetMat;
end;




#TestEquivalenceSublattice:=TestEquivalenceSublattice_V1;
TestEquivalenceSublattice:=TestEquivalenceSublattice_V2;


SUBLATT_SymmetryLiftingList:=function(TheGramMat, SHVbig, ListReturn, GRPmat, AskedGRP)
  local ListMatrGens, ListPermGens, GRPperm, phi, ListAskPermGens, GRPaskedPerm, ListReturnAskGroup, eRecLatt, eStab, ListStabPermGens, GRPstabPerm, eNewLatt, eDCS, ePerm, eMat;
  ListMatrGens:=GeneratorsOfGroup(GRPmat);
  ListPermGens:=List(ListMatrGens, x->PermList(List(SHVbig*x, y->Position(SHVbig, y))));
  GRPperm:=Group(ListPermGens);
  phi:=GroupHomomorphismByImagesNC(GRPperm, GRPmat, ListPermGens, ListMatrGens);
  ListAskPermGens:=List(GeneratorsOfGroup(AskedGRP), x->PermList(List(SHVbig*x, y->Position(SHVbig, y))));
  GRPaskedPerm:=Group(ListPermGens);
  if Order(GRPperm)=Order(GRPaskedPerm) then
    return ListReturn;
  fi;
  ListReturnAskGroup:=[];
  for eRecLatt in ListReturn
  do
    eStab:=GetStabilizerSublattice(TheGramMat, SHVbig, eRecLatt);
    ListStabPermGens:=List(GeneratorsOfGroup(eStab), x->PermList(List(SHVbig*x, y->Position(SHVbig, y))));
    GRPstabPerm:=Group(ListStabPermGens);
    for eDCS in DoubleCosets(GRPperm, GRPstabPerm, GRPaskedPerm)
    do
      ePerm:=Representative(eDCS);
      eMat:=Image(phi, ePerm);
      eNewLatt:=rec(TheLattice:=eRecLatt.TheLattice*eMat, TheDet:=eRecLatt.TheDet, SHV:=eRecLatt.SHV);
      Add(ListReturnAskGroup, eNewLatt);
    od;
  od;
  return ListReturnAskGroup;
end;


#
# This subroutine enumerates the sublattice and does numerous checks in order
# to detect potential problems.
#
GetSublattices_PlusCheck:=function(GramMat, GRP, TheMod)
  local n, ePow, TheRec, SHV, ListRecLatt, TheSum, eRec, ListOrbSize, eGsub, SHVsub, eRecLatt, eStab, OrbSize, GRPtriv, UpdateEntry, nbRec, TheRecB, eRecB, ListOrbSizeB, ListStab;
  n:=Length(GramMat);
  ePow:=(TheMod^n - 1) / (TheMod - 1);
  TheRec:=GetSublattices(GramMat, GRP, TheMod);
  SHV:=__ExtractInvariantZBasisShortVectorNoGroup(GramMat);
  TheSum:=0;
  ListOrbSize:=[];
  ListRecLatt:=[];
  ListStab:=[];
  for eRec in TheRec
  do
    eGsub:=eRec.Basis * GramMat * TransposedMat(eRec.Basis);
    SHVsub:=__ExtractInvariantZBasisShortVectorNoGroup(eGsub);
    eRecLatt:=rec(TheLattice:=eRec.Basis, SHV:=SHVsub, TheDet:=TheMod);
    Add(ListRecLatt, eRecLatt);
    eStab:=GetStabilizerSublattice(GramMat, SHV, eRecLatt);
    Add(ListStab, eStab);
    OrbSize:=Order(GRP) / Order(eStab);
    Add(ListOrbSize, OrbSize);
    TheSum:=TheSum + OrbSize;
  od;
#  Print("ePow=", ePow, " TheSum=", TheSum, "\n");
  if ePow<>TheSum then
    Print("Inconsistency in the computation\n");
    Print("ePow=", ePow, " TheSum=", TheSum, "\n");
    Error("Please correct");
  fi;
  nbRec:=Length(TheRec);
  ListOrbSizeB:=ListWithIdenticalEntries(nbRec, 0);
  UpdateEntry:=function(eSublatt)
    local eGent, SHVent, eRecLattEnt, iRec, test;
    eGent:=eSublatt * GramMat * TransposedMat(eSublatt);
    SHVent:=__ExtractInvariantZBasisShortVectorNoGroup(eGent);
    eRecLattEnt:=rec(TheLattice:=eSublatt, SHV:=SHVent, TheDet:=TheMod);
    for iRec in [1..nbRec]
    do
      test:=TestEquivalenceSublattice(GramMat, SHV, eRecLattEnt, ListRecLatt[iRec]);
      if test<>false then
        ListOrbSizeB[iRec]:=ListOrbSizeB[iRec]+1;
	return;
      fi;
    od;
    Print("We fail to find matching entry in the list\n");
    Print("|Stab|=", Order(GetStabilizerSublattice(GramMat, SHV, eRecLattEnt)), "\n");
    Error("Please correct");
  end;


  GRPtriv:=Group([IdentityMat(n)]);
  TheRecB:=GetSublattices(GramMat, GRPtriv, TheMod);
  for eRecB in TheRecB
  do
    UpdateEntry(eRecB.Basis);
  od;
  if ListOrbSize <> ListOrbSizeB then
    Print("The orbits sizes do not match\n");
    Error("Please correct");
  fi;
  return TheRec;
end;




FullDimensionalEnumeration:=function(FullRecord, TheIndex, RecOpt)
  local TheFile, LFact, MaxPrime, TheIndexRed, ListReturn, FuncInsert, eRecLattRed, eStab, eGen, ListGenRed, eGenRed, eStabRed, GramMatRed, SubList, eRecSub, TheLattice, eG, SHV, eRecLatt, GRPmat, ListReturnFinal, eInv;
  Print("Calling FullDimensionalEnumeration with TheIndex=", TheIndex, "\n");
#  if TheIndex=2 then
#    return 
#  fi;
  if RecOpt.DoSave=true then
    TheFile:=Concatenation(RecOpt.PrefixSave, String(TheIndex));
    if IsExistingFilePlusTouch(TheFile) then
      return ReadAsFunction(TheFile)();
    fi;
  fi;
  if TheIndex=1 then
    return [rec(SHV:=FullRecord.SHV, TheLattice:=IdentityMat(FullRecord.n), TheDet:=1, eInv:="unset")];
  fi;
  LFact:=FactorsInt(TheIndex);
  MaxPrime:=Maximum(LFact);
  TheIndexRed:=TheIndex / MaxPrime;
  ListReturn:=[];
  FuncInsert:=function(eRecLatt)
    local fRecLatt, test;
    for fRecLatt in ListReturn
    do
      if eRecLatt.eInv=fRecLatt.eInv then
        test:=TestEquivalenceSublattice(FullRecord.GramMat, FullRecord.SHV, eRecLatt, fRecLatt);
        if test<>false then
          return;
        fi;
      fi;
    od;
    Add(ListReturn, eRecLatt);
    Print("Now we have |ListReturn|=", Length(ListReturn), " at Index=", TheIndex, "\n");
  end;
  for eRecLattRed in FullDimensionalEnumeration(FullRecord, TheIndexRed, RecOpt)
  do
    eStab:=GetStabilizerSublattice(FullRecord.GramMat, FullRecord.SHV, eRecLattRed);
    ListGenRed:=[];
    for eGen in GeneratorsOfGroup(eStab)
    do
      eGenRed:=List(eRecLattRed.TheLattice, x->SolutionMat(eRecLattRed.TheLattice, x*eGen));
      if IsIntegralMat(eGenRed)=false then
        Error("The matrix should be integral because it should preserve the lattice");
      fi;
      Add(ListGenRed, eGenRed);
    od;
    eStabRed:=Group(ListGenRed);
    Print("|eStab|=", Order(eStab), " |eStabRed|=", Order(eStabRed), "\n");
    GramMatRed:=eRecLattRed.TheLattice * FullRecord.GramMat * TransposedMat(eRecLattRed.TheLattice);
    SubList:=GetSublattices(GramMatRed, eStabRed, MaxPrime);
#     Below is running with additional checks.
#    SubList:=GetSublattices_PlusCheck(GramMatRed, eStabRed, MaxPrime);
    for eRecSub in SubList
    do
      TheLattice:=eRecSub.Basis * eRecLattRed.TheLattice;
      eG:=TheLattice * FullRecord.GramMat * TransposedMat(TheLattice);
      SHV:=__ExtractInvariantZBasisShortVectorNoGroup(eG);
      eInv:=GetInvariantSublattice(FullRecord.GramMat, FullRecord.SHV, rec(SHV:=SHV, TheLattice:=TheLattice));
      eRecLatt:=rec(SHV:=SHV, TheLattice:=TheLattice, TheDet:=TheIndex, eInv:=eInv);
      FuncInsert(eRecLatt);
    od;
  od;
  if RecOpt.DoSave=true then
    TheFile:=Concatenation(RecOpt.PrefixSave, String(TheIndex));
    SaveDataToFilePlusTouch(TheFile, ListReturn);
  fi;
  return ListReturn;
end;










GENERIC_ProcEnum_SublatticeEnumeration:=function(eRecFCT)
  local ListDatabaseSolutions, FuncGetSolution, DoSpecificEnumeration, GetDatabaseSolution, EnumerateSublattices;
  ListDatabaseSolutions:=[];
  GetDatabaseSolution:=function()
    return ListDatabaseSolutions;
  end;
  FuncGetSolution:=function(TheGramMat, SHVbig, AskedGRP, TheDim, TheDet)
    local eRecSolution, eEquiv, NewListReturn, eRecLatt, eNewLatt, GRPmat, TheDetTest;
#    Print("|ListDatabaseSolutions|=", Length(ListDatabaseSolutions), "\n");
    for eRecSolution in ListDatabaseSolutions
    do
      if eRecSolution.TheDim=TheDim and eRecSolution.TheDet=TheDet and DeterminantMat(TheGramMat)=DeterminantMat(eRecSolution.GramMat) and Length(TheGramMat)=Length(eRecSolution.GramMat) then
        eEquiv:=ArithmeticEquivalenceMatrixFamily_HackSouvignier_V2("", [TheGramMat], SHVbig, [eRecSolution.GramMat], eRecSolution.SHV);
#        eEquiv:=ArithmeticEquivalenceMatrixFamily_Nauty([TheGramMat], SHVbig, [eRecSolution.GramMat], eRecSolution.SHV);
        if eEquiv<>false then
          NewListReturn:=[];
          for eRecLatt in eRecSolution.ListReturn
          do
            eNewLatt:=rec(TheLattice:=eRecLatt.TheLattice*eEquiv, SHV:=eRecLatt.SHV, TheDet:=eRecLatt.TheDet);
            TheDetTest:=DeterminantMat(eNewLatt.TheLattice*TheGramMat*TransposedMat(eNewLatt.TheLattice));
            if TheDetTest<>eNewLatt.TheDet then
              Error("We have a bug to hunt");
            fi;
            Add(NewListReturn, eNewLatt);
          od;
          GRPmat:=ArithmeticAutomorphismMatrixFamily_HackSouvignier_V2("", [TheGramMat], SHVbig);
#          GRPmat:=ArithmeticAutomorphismMatrixFamily_Nauty([TheGramMat],SHVbig);
          return SUBLATT_SymmetryLiftingList(TheGramMat, SHVbig, NewListReturn, GRPmat, AskedGRP);
        fi;
      fi;
    od;
    return false;
  end;
  DoSpecificEnumeration:=function(TheGramMat, SHVbig, AskedGRP, TheDim, TheDet)
    local eRec, GRP, n, SHVunpair, SHV, O, ListReturn, eO, eVect, eDet, eRecLatt, TheReply, TheDeterminQuant, MaxVal, GRPmat, FuncInsert, rNorm, TheCompl, TheProj, fVect, rVect, ReducedGramMat, TheStab, ListMatGens, TheExtStab, TheAskDet, InvBasisRed, eBigLatt, eProdMat, InvariantBasis, eRecLattice, eRecSolution, SpecEnum, eGen, eSmallMat, eLine, eSol, TheSumDirect;
    eRec:=RemoveFractionMatrixPlusCoef(TheGramMat);
#    Print("(", Length(TheGramMat), ",", TheDim, ") TheDet=", TheDet, " |SHV|=", Length(SHVbig), " |GRP|=", Order(AskedGRP), "\n");
    for eGen in GeneratorsOfGroup(AskedGRP)
    do
      if eGen*TheGramMat*TransposedMat(eGen)<>TheGramMat then
        Error("Inconsistency in your function call, the group should preserve the gram matrix");
      fi;
    od;
    n:=Length(TheGramMat);
    if TheDim=1 then
      SHVunpair:=ShortestVectors(eRec.TheMat, LowerInteger(TheDet*eRec.TheMult));
      SHV:=Concatenation(SHVunpair.vectors, -SHVunpair.vectors);
      O:=Orbits(AskedGRP, SHV, OnPoints);
      ListReturn:=[];
      for eO in O
      do
        eVect:=eO[1];
        eDet:=eVect*TheGramMat*eVect;
        eRecLatt:=rec(TheLattice:=[eO[1]], SHV:=[[1],[-1]], TheDet:=eDet/eRec.TheMult);
        Add(ListReturn, eRecLatt);
      od;
      return ListReturn;
    fi;
    TheReply:=FuncGetSolution(TheGramMat, SHVbig, AskedGRP, TheDim, TheDet);
    if TheReply<>false then
      return TheReply;
    fi;
    TheDeterminQuant:=eRecFCT.LegalHermiteConstant(TheDim)*TheDet*((eRec.TheMult)^(TheDim));
    if TheDeterminQuant < 1 then
      MaxVal:=1/2; # it will be empty set everywhere
    else
      MaxVal:=GetLowestPower(TheDim, TheDeterminQuant);
    fi;
    GRPmat:=ArithmeticAutomorphismMatrixFamily_HackSouvignier_V2("", [eRec.TheMat], SHVbig);
#    GRPmat:=ArithmeticAutomorphismMatrixFamily_Nauty([eRec.TheMat], SHVbig);
    SHVunpair:=ShortestVectors(eRec.TheMat, MaxVal);
    SHV:=Concatenation(SHVunpair.vectors, -SHVunpair.vectors);
    O:=Orbits(GRPmat, SHV, OnPoints);
    ListReturn:=[];
    FuncInsert:=function(eRecLattice)
      local fRecLattice, test;
      for fRecLattice in ListReturn
      do
        if fRecLattice.TheDet=eRecLattice.TheDet then
          test:=TestEquivalenceSublattice([TheGramMat], SHVbig, eRecLattice, fRecLattice);
          if test<>false then
            return;
          fi;
        fi;
      od;
      Add(ListReturn, eRecLattice);
    end;
    for eO in O
    do
      eVect:=eO[1];
      rNorm:=eVect*TheGramMat*eVect;
      TheCompl:=eRecFCT.GetLegalComplementBasis(TheGramMat, eVect);
      TheProj:=[];
      for fVect in TheCompl
      do
        rVect:=fVect - eVect*((eVect*TheGramMat*fVect)/rNorm);
        Add(TheProj, rVect);
      od;
      TheSumDirect:=Concatenation([eVect], TheCompl);
      ReducedGramMat:=TheProj*TheGramMat*TransposedMat(TheProj);
      TheStab:=Stabilizer(AskedGRP, eVect, OnPoints);
      ListMatGens:=[];
      for eGen in Concatenation([-IdentityMat(n)], GeneratorsOfGroup(TheStab))
      do
        eSmallMat:=[];
        for eLine in TheCompl
        do
          eSol:=SolutionMat(TheSumDirect, eLine*eGen);
          Add(eSmallMat, eSol{[2..n]});
        od;
        Add(ListMatGens, eSmallMat);
      od;
      TheExtStab:=Group(ListMatGens);
      InvBasisRed:=__ExtractInvariantZBasisShortVectorNoGroup(ReducedGramMat);
      TheAskDet:=TheDet/rNorm;
      SpecEnum:=DoSpecificEnumeration(ReducedGramMat, InvBasisRed, TheExtStab, TheDim-1, TheAskDet);
      for eRecLattice in SpecEnum
      do
        eBigLatt:=Concatenation([eVect], eRecLattice.TheLattice*TheCompl);
        if RankMat(eBigLatt)<>TheDim then
          Error("Clear inconsistency that needs to be solved");
        fi;
        eProdMat:=eBigLatt*TheGramMat*TransposedMat(eBigLatt);
        eDet:=DeterminantMat(eProdMat);
        if eDet<=TheDet then
          InvariantBasis:=__ExtractInvariantZBasisShortVectorNoGroup(eProdMat);
	  if AbsInt(DeterminantMat(BaseIntMat(InvariantBasis)))<>1 then
	    Error("The determinant should be 1\n");
	  fi;
          eRecLattice:=rec(TheLattice:=eBigLatt, SHV:=InvariantBasis, TheDet:=eDet);
          FuncInsert(eRecLattice);
        else
          Error("Probably we have some inconsistency. The determinant should match the bound");
        fi;
      od;
    od;
    eRecSolution:=rec(GramMat:=TheGramMat, SHV:=SHVbig, TheDim:=TheDim, TheDet:=TheDet, ListReturn:=ListReturn);
    Add(ListDatabaseSolutions, eRecSolution);
    return SUBLATT_SymmetryLiftingList(TheGramMat, SHVbig,ListReturn, GRPmat, AskedGRP);
  end;
  EnumerateSublattices:=function(TheGramMat, TheDim, TheDet)
    local SHVbig, GRPmat;
    SHVbig:=__ExtractInvariantZBasisShortVectorNoGroup(TheGramMat);
    GRPmat:=ArithmeticAutomorphismMatrixFamily_HackSouvignier_V2("", [TheGramMat], SHVbig);
#    GRPmat:=ArithmeticAutomorphismMatrixFamily_Nauty([TheGramMat], SHVbig);
    return DoSpecificEnumeration(TheGramMat, SHVbig, GRPmat, TheDim, TheDet);
  end;
  return rec(DoSpecificEnumeration:=DoSpecificEnumeration, 
             EnumerateSublattices:=EnumerateSublattices, 
             GetDatabaseSolution:=GetDatabaseSolution);
end;




ProcEnum_SublatticeEnumeration:=function()
  local eRecFCT, GetLegalComplementBasis, LegalHermiteConstant;
  GetLegalComplementBasis:=function(GramMat, eVect)
    local n;
    n:=Length(eVect);
    return SubspaceCompletion([RemoveFraction(eVect)], n);
  end;
  LegalHermiteConstant:=function(n)
    return GetHermitePower(n);
  end;
  eRecFCT:=rec(GetLegalComplementBasis:=GetLegalComplementBasis, 
               LegalHermiteConstant:=LegalHermiteConstant);
  return GENERIC_ProcEnum_SublatticeEnumeration(eRecFCT);
end;


CreateFileDiagram:=function(n, ListDet, eFileOUT)
  local eFileIN, output, i;
  eFileIN:=Filename(POLYHEDRAL_tmpdir,"Grayson.in");
  RemoveFileIfExist(eFileIN);
  output:=OutputTextFile(eFileIN, true);;
  AppendTo(output, n, "\n");
  for i in [1..n]
  do
    AppendTo(output, ListDet[i], "\n");
  od;
  CloseStream(output);
  Exec(FileGraysonDiagram, " ", eFileIN," > ", eFileOUT);
end;



ProcEnum_OrthonormalEnumeration:=function()
  local eRecFCT, GetLegalComplementBasis, LegalHermiteConstant;
  GetLegalComplementBasis:=function(GramMat, eVect)
    return NullspaceIntMat(TransposedMat([eVect*RemoveFractionMatrix(GramMat)]));
  end;
  LegalHermiteConstant:=function(n)
    return 1;
  end;
  eRecFCT:=rec(GetLegalComplementBasis:=GetLegalComplementBasis, 
               LegalHermiteConstant:=LegalHermiteConstant);
  return GENERIC_ProcEnum_SublatticeEnumeration(eRecFCT);
end;




StabEnum_GetMaximalDetStability:=function(k, n, TheDetN)
  local p, a, b, c;
  p:=1;
  while(true)
  do
    a:=(p+1)^n;
    b:=(TheDetN)^k;
    c:=a-b;
    if c>=0 then
      return p;
    fi;
    p:=p+1;
  od;
end;


IsStableLatticeGRP:=function(ProcEnum, TheGramMat, SHVbig, GRPmat)
  local n, TheDetN, TheDim, MaxDet, ListCases, eCase, TheDetCertif, ListString, eStr, GramCertif, i, eLine;
  n:=Length(TheGramMat);
  if IsIntegralMat(TheGramMat)=false then
    Error("For stability, we need integrality");
  fi;
  TheDetN:=DeterminantMat(TheGramMat);
  if TheDetN=1 then
    return true;
  fi;
  for TheDim in [1..n-1]
  do
    MaxDet:=StabEnum_GetMaximalDetStability(TheDim, n, TheDetN);
    ListCases:=ProcEnum.DoSpecificEnumeration(TheGramMat, SHVbig, GRPmat, TheDim, MaxDet);
    if Length(ListCases)>0 then
      eCase:=ListCases[1];
      ListString:=[];
      Add(ListString, "  proof of non-stability is sublattice spanned by:");
      for eLine in eCase.TheLattice
      do
        eStr:="  [";
        for i in [1..n]
        do
          if i>1 then
            eStr:=Concatenation(eStr, ",");
          fi;
          eStr:=Concatenation(eStr, String(eLine[i]));
        od;
        eStr:=Concatenation(eStr, "]");
        Add(ListString, eStr);
      od;
      GramCertif:=eCase.TheLattice*TheGramMat*TransposedMat(eCase.TheLattice);
      TheDetCertif:=DeterminantMat(GramCertif);
      Add(ListString, Concatenation("  of determinant ", String(TheDetCertif)));
      Add(ListString, Concatenation("  and ", String(TheDetCertif), "^{", String(n), "} < ", String(TheDetN), "^{", String(TheDim), "}"));
      return rec(Answer:=false, Certificate:=ListString);
    fi;
  od;
  return rec(Answer:=true, Certificate:="nothing simple");
end;

IsStableLattice:=function(ProcEnum, TheGramMat)
  local SHVbig, GRPmat;
  SHVbig:=__ExtractInvariantZBasisShortVectorNoGroup(TheGramMat);
  GRPmat:=ArithmeticAutomorphismMatrixFamily_HackSouvignier_V2("", [TheGramMat], SHVbig);
#  GRPmat:=ArithmeticAutomorphismMatrixFamily_Nauty([TheGramMat], SHVbig);
  return IsStableLatticeGRP(ProcEnum, TheGramMat, SHVbig, GRPmat);
end;



ComputeOrbitSublattice:=function(GRPmat, wLatt)
  local ListReturn, ListActive, FuncInsert, IsFinished, len, i, eMatrGen, eImgLatt;
  ListReturn:=[wLatt];
  ListActive:=[1];
  FuncInsert:=function(eLatt)
    local fLatt;
    for fLatt in ListReturn
    do
      if IsEquivalentRepresentationSublattice(eLatt, fLatt)=true then
        return;
      fi;
    od;
    Add(ListReturn, eLatt);
    Add(ListActive, 1);
  end;
  while(true)
  do
    IsFinished:=true;
    len:=Length(ListActive);
#    Print("len=", len, "\n");
    for i in [1..len]
    do
      if ListActive[i]=1 then
        ListActive[i]:=0;
        IsFinished:=false;
        for eMatrGen in GeneratorsOfGroup(GRPmat)
        do
          eImgLatt:=ListReturn[i]*eMatrGen;
          FuncInsert(eImgLatt);
        od;
      fi;
    od;
    if IsFinished=true then
      break;
    fi;
  od;
#  Print("Enumeration finished\n");
  return ListReturn;
end;

UpperBoundRankinMinimalDeterminant:=function(TheGramMat, k)
  local n, SHVmin, eVect, TheCompl, TheProj, fVect, ReducedGramMat, rVect, rNorm;
  n:=Length(TheGramMat);
  SHVmin:=ShortestVectorDutourVersion(TheGramMat);
  eVect:=SHVmin[1];
  rNorm:=eVect*TheGramMat*eVect;
  if k=1 then
    return eVect*TheGramMat*eVect;
  fi;
  TheCompl:=SubspaceCompletion([eVect], n);
  TheProj:=[];
  for fVect in TheCompl
  do
    rVect:=fVect - eVect*((eVect*TheGramMat*fVect)/rNorm);
    Add(TheProj, rVect);
  od;
  ReducedGramMat:=TheProj*TheGramMat*TransposedMat(TheProj);
  return rNorm*UpperBoundRankinMinimalDeterminant(ReducedGramMat, k-1);
end;


#
# The orthogonal projection is defined by
# If the subspace is spanned by x1
GetAllRankinConstants:=function(TheGramMat)
  local SHVbig, GRPmat, ProcEnum, n, ListSolution, k, SHVmin, eVect, rNorm, TheUppEst, TheReply, ListUppEst, eCase, NSP, eGram, i, j, TheCompl, eRecInfo, ListCases, PreListCases, CritQuot, MinDet, ListDet, eUppEst, eMinReduced, eVectReduced, SHVreduced, TheProj, ReducedGramMat, xProj, eSol, Bside, eGramInv, fVect, hDim;
  SHVbig:=__ExtractInvariantZBasisShortVectorNoGroup(TheGramMat);
  GRPmat:=ArithmeticAutomorphismMatrixFamily_HackSouvignier_V2("", [TheGramMat], SHVbig);
#  GRPmat:=ArithmeticAutomorphismMatrixFamily_Nauty([TheGramMat], SHVbig);
  ProcEnum:=ProcEnum_SublatticeEnumeration();
  n:=Length(TheGramMat);
  ListSolution:=[];
  for k in [1..n-1]
  do
    if k=1 then
      SHVmin:=ShortestVectorDutourVersion(TheGramMat);
      eVect:=SHVmin[1];
      rNorm:=eVect*TheGramMat*eVect;
      TheUppEst:=rNorm;
    else
      ListUppEst:=[];
      for eCase in ListSolution[k-1].ListCases
      do
        NSP:=NullspaceMat(TransposedMat(eCase.TheLattice*TheGramMat));
        hDim:=n - (k-1);
        eGram:=NullMat(hDim, hDim);
        for i in [1..hDim]
        do
          for j in [1..hDim]
          do
            eGram[i][j]:=NSP[i]*TheGramMat*NSP[j];
          od;
        od;
        TheCompl:=SubspaceCompletion(eCase.TheLattice, n);
        eGramInv:=Inverse(eGram);
        TheProj:=[];
        for fVect in TheCompl
        do
          Bside:=List(NSP, x->x*TheGramMat*fVect);
          eSol:=Bside*eGramInv;
          xProj:=ListWithIdenticalEntries(n,0);
          for j in [1..hDim]
          do
            xProj:=xProj + eSol[j]*NSP[j];
          od;
          Add(TheProj, xProj);
        od;
        ReducedGramMat:=TheProj*TheGramMat*TransposedMat(TheProj);
        SHVreduced:=ShortestVectorDutourVersion(ReducedGramMat);
        eVectReduced:=SHVreduced[1];
        eMinReduced:=eVectReduced*ReducedGramMat*eVectReduced;
        eUppEst:=eMinReduced*eCase.TheDet;
        Add(ListUppEst, eUppEst);
      od;
      TheUppEst:=Minimum(ListUppEst);
    fi;
    PreListCases:=ProcEnum.DoSpecificEnumeration(TheGramMat, SHVbig, GRPmat, k, TheUppEst);
    ListDet:=List(PreListCases, x->x.TheDet);
    MinDet:=Minimum(ListDet);
    ListCases:=Filtered(PreListCases, x->x.TheDet=MinDet);
    CritQuot:=(MinDet^n)/(Determinant(TheGramMat)^k);
    eRecInfo:=rec(ListCases:=ListCases, 
                  CritQuot:=CritQuot, 
                  TheDet:=MinDet);
    Print("k=", k, " MinDet=", MinDet, " TheUppEst=", TheUppEst, " |ListCases|=", Length(ListCases), "\n");
    Add(ListSolution, eRecInfo);
  od;
  return ListSolution;
end;



RankinGetOrbitMinimalSublatticesGRP:=function(ProcEnum, TheGramMat, k, SHVbig, GRPmat)
  local SHVmin, TheMin, TheMinDetAtp, TheMinDet, ListCases, MinDet, ListDet, ListCasesRet, TheUppEst, UseMethod1, UseMethod2;
  SHVmin:=ShortestVectorDutourVersion(TheGramMat);
  TheMin:=Minimum(List(SHVmin, x->x*TheGramMat*x));
  TheUppEst:=UpperBoundRankinMinimalDeterminant(TheGramMat, k);
  TheMinDetAtp:=TheMin^k/GetHermitePower(k);
  UseMethod1:=false;
  if UseMethod1=true then
    TheMinDet:=TheUppEst;
    while(true)
    do
      Print("k=", k, " TheMinDet=", TheMinDet, " TheMinDetAtp=", TheMinDetAtp, " eUppEst=", TheUppEst, "\n");
      ListCases:=ProcEnum.DoSpecificEnumeration(TheGramMat, SHVbig, GRPmat, k, TheMinDet);
      if Length(ListCases)>0 then
        ListDet:=List(ListCases, x->x.TheDet);
        MinDet:=Minimum(ListDet);
        ListCasesRet:=Filtered(ListCases, x->x.TheDet=MinDet);
        Print("k=", k, " MinDet=", MinDet, " TheUppEst=", TheUppEst, "\n");
        return ListCasesRet;
      fi;
      TheMinDet:=TheMinDet+1;
    od;
  fi;
  UseMethod2:=true;
  if UseMethod2=true then
    TheMinDet:=TheUppEst;
    ListCases:=ProcEnum.DoSpecificEnumeration(TheGramMat, SHVbig, GRPmat, k, TheMinDet);
    if Length(ListCases)>0 then
      ListDet:=List(ListCases, x->x.TheDet);
      MinDet:=Minimum(ListDet);
      ListCasesRet:=Filtered(ListCases, x->x.TheDet=MinDet);
      Print("k=", k, " MinDet=", MinDet, " TheUppEst=", TheUppEst, "\n");
      return ListCasesRet;
    fi;
  fi;
end;


GetSublatticesOfSpecifiedRankMaxDet:=function(TheGramMat, k, MaxDet)
  local SHVbig, GRPmat, ProcEnum, ListCases, ListReturn, eCaseLatt, ListLatt;
  SHVbig:=__ExtractInvariantZBasisShortVectorNoGroup(TheGramMat);
  GRPmat:=ArithmeticAutomorphismMatrixFamily_HackSouvignier_V2("", [TheGramMat], SHVbig);
#  GRPmat:=ArithmeticAutomorphismMatrixFamily_Nauty([TheGramMat], SHVbig);
  ProcEnum:=ProcEnum_SublatticeEnumeration();
  ListCases:=ProcEnum.DoSpecificEnumeration(TheGramMat, SHVbig, GRPmat, k, MaxDet);
  ListReturn:=[];
  for eCaseLatt in ListCases
  do
    ListLatt:=ComputeOrbitSublattice(GRPmat, eCaseLatt.TheLattice);
    Append(ListReturn, ListLatt);
  od;
  return ListReturn;
end;

RankinPerfectionRank_V1:=function(TheGramMat, GRPmat, ListCases)
  local ListSymmetricMatrix, k, eCaseLatt, ListLatt, eLatt, TheProd, eMatrix, TheSpace, eSymmVect;
  ListSymmetricMatrix:=[];
  k:=Length(ListCases[1].TheLattice);
  for eCaseLatt in ListCases
  do
    ListLatt:=ComputeOrbitSublattice(GRPmat, eCaseLatt.TheLattice);
    for eLatt in ListLatt
    do
      TheProd:=eLatt*TheGramMat*TransposedMat(eLatt);
      eMatrix:=TransposedMat(eLatt)*Inverse(TheProd)*eLatt;
      eSymmVect:=SymmetricMatrixToVector(eMatrix);
      Add(ListSymmetricMatrix, eSymmVect);
    od;
  od;
  TheSpace:=GetTransposeNullspaceMat(ListSymmetricMatrix);
  return Length(TheSpace);
end;



RankinPerfectionRank_V2:=function(TheGramMat, GRPmat, ListCases)
  local n, TheBasis, eLatt, TheProd, eMatrix, eSymmVect, NewListGens, TheGRPsymm, MatDim, TheBasisSpann, eCaseLatt;
  n:=Length(TheGramMat);
  TheBasis:=[];
  for eCaseLatt in ListCases
  do
    eLatt:=eCaseLatt.TheLattice;
    TheProd:=eLatt*TheGramMat*TransposedMat(eLatt);
    eMatrix:=TransposedMat(eLatt)*Inverse(TheProd)*eLatt;
    eSymmVect:=SymmetricMatrixToVector(eMatrix);
    Add(TheBasis, eSymmVect);
  od;
  NewListGens:=List(GeneratorsOfGroup(GRPmat), MatrixTransformationMappingToSymmetricMatrix);
  TheGRPsymm:=Group(NewListGens);
  MatDim:=n*(n+1)/2;
  TheBasisSpann:=DirectSpannEquivariantSpace(TheBasis, TheGRPsymm);
  return MatDim - Length(TheBasisSpann);
end;

#RankinPerfectionRank:=RankinPerfectionRank_V1;
RankinPerfectionRank:=RankinPerfectionRank_V2;




RankinEutacticity_V1:=function(TheGramMat, GRPmat, ListCases)
  local ListSymmetricMatrix, k, ListStrictlyPositive, eCaseLatt, ListLatt, eLatt, TheProd, eMatrix, eSymmVect, idx, TheConstraint, TheResult;
  ListSymmetricMatrix:=[];
  k:=Length(ListCases[1].TheLattice);
  ListStrictlyPositive:=[];
  idx:=0;
  for eCaseLatt in ListCases
  do
    ListLatt:=ComputeOrbitSublattice(GRPmat, eCaseLatt.TheLattice);
    for eLatt in ListLatt
    do
      TheProd:=eLatt*TheGramMat*TransposedMat(eLatt);
      eMatrix:=TransposedMat(eLatt)*Inverse(TheProd)*eLatt;
      eSymmVect:=SymmetricMatrixToVector(eMatrix);
      Add(ListSymmetricMatrix, eSymmVect);
      idx:=idx+1;
      Add(ListStrictlyPositive, idx);
    od;
  od;
  eSymmVect:=SymmetricMatrixToVector(Inverse(TheGramMat));
  Add(ListSymmetricMatrix, -eSymmVect);
  idx:=idx+1;
  Add(ListStrictlyPositive, idx);
  #
  TheConstraint:=rec(ListStrictlyPositive:=ListStrictlyPositive,
                     ListPositive:=[], 
                     ListSetStrictPositive:=[]);
  TheResult:=SearchPositiveRelation(ListSymmetricMatrix, TheConstraint);
  if TheResult<>false then
    return true;
  fi;
  return false;
end;


RankinEutacticity_V2:=function(TheGramMat, GRPmat, ListCases)
  local NewListGens, TheGRPsymm, eLatt, TheProd, eMatrix, eSymmVect, eSymmIso, len, ListStrictlyPositive, TheConstraint, TheResult, eCaseLatt, TheListIsobarycenters;
  NewListGens:=List(GeneratorsOfGroup(GRPmat), MatrixTransformationMappingToSymmetricMatrix);
  TheGRPsymm:=Group(NewListGens);
  TheListIsobarycenters:=[];
  for eCaseLatt in ListCases
  do
    eLatt:=eCaseLatt.TheLattice;
    TheProd:=eLatt*TheGramMat*TransposedMat(eLatt);
    eMatrix:=TransposedMat(eLatt)*Inverse(TheProd)*eLatt;
    eSymmVect:=SymmetricMatrixToVector(eMatrix);
    eSymmIso:=OrbitBarycenter(eSymmVect, TheGRPsymm).TheBarycenter;
    Add(TheListIsobarycenters, eSymmIso);
  od;
  eSymmVect:=SymmetricMatrixToVector(Inverse(TheGramMat));
  Add(TheListIsobarycenters, -eSymmVect);
  len:=Length(TheListIsobarycenters);
  ListStrictlyPositive:=[1..len];
  #
  TheConstraint:=rec(ListStrictlyPositive:=ListStrictlyPositive,
                     ListPositive:=[], 
                     ListSetStrictPositive:=[]);
  TheResult:=SearchPositiveRelation(TheListIsobarycenters, TheConstraint);
  if TheResult<>false then
    return true;
  fi;
  return false;
end;



#RankinEutacticity:=RankinEutacticity_V1;
RankinEutacticity:=RankinEutacticity_V2;





RankinAllComputations:=function(ProcEnum, k, TheGramMat)
  local SHVbig, GRPmat, ListCases, RankinPerfRank, IsRankinPerf, IsRankinEuct, GetListStabilizer, GetPerfectCone, TheDet;
  SHVbig:=__ExtractInvariantZBasisShortVectorNoGroup(TheGramMat);
  GRPmat:=ArithmeticAutomorphismMatrixFamily_HackSouvignier_V2("", [TheGramMat], SHVbig);
#  GRPmat:=ArithmeticAutomorphismMatrixFamily_Nauty([TheGramMat], SHVbig);
  ListCases:=RankinGetOrbitMinimalSublatticesGRP(ProcEnum, TheGramMat, k, SHVbig, GRPmat);
  TheDet:=ListCases[1].TheDet;
#  Print("ListCases=", ListCases, "\n");
  RankinPerfRank:=RankinPerfectionRank(TheGramMat, GRPmat, ListCases);
  IsRankinEuct:=RankinEutacticity(TheGramMat, GRPmat, ListCases);
  IsRankinPerf:=RankinPerfRank=0;
  GetListStabilizer:=function()
    local ListStab, eCaseLatt, eStab;
    ListStab:=[];
    for eCaseLatt in ListCases
    do
      eStab:=GetStabilizerSublattice(TheGramMat, SHVbig, eCaseLatt);
      Add(ListStab, eStab);
    od;
    return ListStab;
  end;
  GetPerfectCone:=function()
    local ListSymmVect, eCaseLatt, ListLatt, eLatt, TheProd, eMatrix, eSymmVect, ListMatrGens, ListPermGens, eGen, eGenP, eGenSymm, eList, eGenPerm, GRPperm, ListSymmMat, ListLattices;
    ListSymmVect:=[];
    ListSymmMat:=[];
    ListLattices:=[];
    for eCaseLatt in ListCases
    do
      ListLatt:=ComputeOrbitSublattice(GRPmat, eCaseLatt.TheLattice);
      Append(ListLattices, ListLatt);
      for eLatt in ListLatt
      do
        TheProd:=eLatt*TheGramMat*TransposedMat(eLatt);
        eMatrix:=TransposedMat(eLatt)*Inverse(TheProd)*eLatt;
        eSymmVect:=SymmetricMatrixToVector(eMatrix);
        Add(ListSymmVect, eSymmVect);
        Add(ListSymmMat, eMatrix);
      od;
    od;
    ListMatrGens:=[];
    ListPermGens:=[];
    for eGen in GeneratorsOfGroup(GRPmat)
    do
      eGenP:=TransposedMat(eGen);
      eGenSymm:=MatrixTransformationMappingToSymmetricMatrix(eGenP);
      Add(ListMatrGens, eGenSymm);
      eList:=List(ListSymmMat, x->Position(ListSymmMat, eGenP*x*eGen));
      eGenPerm:=PermList(eList);
      Add(ListPermGens, eGenPerm);
    od;
    GRPperm:=Group(ListPermGens);
    return rec(GRPperm:=GRPperm, 
               ListLattices:=ListLattices,
               ListSymmMat:=ListSymmMat,
               ListSymmVect:=ListSymmVect);
  end;
  return rec(SHVbig:=SHVbig, 
             GRPmat:=GRPmat, 
             ListCases:=ListCases, 
             TheDet:=TheDet, 
             n:=Length(TheGramMat), 
             k:=k,
             RankinPerfRank:=RankinPerfRank,
             IsRankinPerf:=IsRankinPerf, 
             IsRankinEuct:=IsRankinEuct, 
             GetPerfectCone:=GetPerfectCone, 
             GetListStabilizer:=GetListStabilizer);
end;



Rankin_WriteToC_EnumConfig:=function(FileSave, TheGramMat, k, MaxDet)
  local output, i, j, n;
  n:=Length(TheGramMat);
  RemoveFileIfExist(FileSave);
  output:=OutputTextFile(FileSave, true);
  AppendTo(output, k, "\n");
  AppendTo(output, GetFractionAsReal(MaxDet), "\n");
  AppendTo(output, Length(TheGramMat), "\n");
  for i in [1..n]
  do
    for j in [1..n]
    do
      AppendTo(output, " ", GetFractionAsReal(TheGramMat[i][j]));
    od;
    AppendTo(output, "\n");
  od;
  CloseStream(output);
end;


Rankin_WriteToC_Flipping:=function(FileSave, TheGramMat, k, DirMat)
  local output, i, j, n;
  n:=Length(TheGramMat);
  RemoveFileIfExist(FileSave);
  output:=OutputTextFile(FileSave, true);
  AppendTo(output, k, "\n");
  AppendTo(output, Length(TheGramMat), "\n");
  for i in [1..n]
  do
    for j in [1..n]
    do
      AppendTo(output, " ", GetFractionAsReal(TheGramMat[i][j]));
    od;
    AppendTo(output, "\n");
  od;
  for i in [1..n]
  do
    for j in [1..n]
    do
      AppendTo(output, " ", GetFractionAsReal(DirMat[i][j]));
    od;
    AppendTo(output, "\n");
  od;
  CloseStream(output);
end;

GetSublatticeByLinearForm:=function(LinForm, TheIndex)
  local Block1, RecGcd, eQuot;
  Block1:=NullspaceIntMat(TransposedMat([LinForm]));
  RecGcd:=GcdVector(LinForm);
  eQuot:=TheIndex/RecGcd.TheGcd;
  if IsInt(eQuot)=false then
    Print("The quotient eQuot=", eQuot, " is not integral\n");
    Error("Please correct");
  fi;
  return Concatenation(Block1, [eQuot*RecGcd.ListCoef]);
end;
