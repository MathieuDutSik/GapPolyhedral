FileCompCovDens:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"ComputeCoveringDensity");
FileCompEngelSymbol:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"POLY_ComputeEngelSymbol");
FileFaceLattice:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"POLY_FaceLatticeDirect");

GetClassificationLatticeDelaunayPolytopes:=function(n)
  local eDir, eFile;
  if n>6 then
    Error("Results are not known beyond dimension 7");
  fi;
  eDir:=DirectoriesPackageLibrary("MyPolyhedral", "DATA/DelaunayPolytope")[1];
  eFile:=Filename(eDir, Concatenation("ListDelaunay", String(n)));
  return ReadAsFunction(eFile)();
end;



ListFactors:=function(eVect)
  local eLcm, eVal;
  eLcm:=1;
  for eVal in eVect
  do
    eLcm:=LcmInt(DenominatorRat(eVal), eLcm);
  od;
  return eLcm;
end;

SymmetricMatrixOccurences:=function(DM)
  local ListValue, ListOcc, i, j, Val, pos;
  ListValue:=[];
  ListOcc:=[];
  for i in [1..Length(DM)-1]
  do
    for j in [i+1..Length(DM)]
    do
      Val:=DM[i][j];
      pos:=Position(ListValue, Val);
      if pos=fail then
        Add(ListValue, Val);
        Add(ListOcc, 1);
      else
        ListOcc[pos]:=ListOcc[pos]+1;
      fi;
    od;
  od;
  return Set(List([1..Length(ListValue)], x->[ListValue[x], ListOcc[x]]));
end;

DelaunayInvariantLattice:=function(DataLattice, EXT)
  local CP, LFactors, TheDet, DistInvariant, eIso, test, rnk;
  if Length(EXT) < 200 then
    DistInvariant:=SymmetricMatrixOccurences(DistanceMatrixDelaunay(DataLattice.GramMat, EXT));
  else
    DistInvariant:="undefined";
  fi;
  #
  CP:=CenterRadiusDelaunayPolytopeGeneral(DataLattice.GramMat, EXT);
  if IsVectorRational(CP.Center) then
    LFactors:=ListFactors(CP.Center);
  else
    LFactors:="undefined";
  fi;
  #
  eIso:=Isobarycenter(EXT);
  test:=eIso=CP.Center;
  #
  rnk:=RankMat(EXT);
  if rnk=Length(EXT[1]) then
    TheDet:=DeterminantMat(BaseIntMat(EXT));
  else
    # actually we can do something here
    TheDet:="undefined";
  fi;
  return rec(nbV:=Length(EXT), DistInvariant:=DistInvariant, LFactors:=LFactors, TheDet:=TheDet, RankMat:=rnk, Radius:=CP.SquareRadius, test:=test);
end;


VectorModPW:=function(eVect, pw)
  local NewV, i, a, b;
  NewV:=[];
  for i in [1..Length(eVect)]
  do
    b:=NumeratorRat(eVect[i]);
    a:=DenominatorRat(eVect[i]);
    Add(NewV, ((b*pw) mod a)/(a*pw));
  od;
  return NewV;
end;

CharacterizingPair:=function(GramMat, TheCenter)
  local n, TheCenterRed, Mat1, i, j, eVect, Mat2, MatRet1, eScal;
  n:=Length(GramMat);
  TheCenterRed:=TheCenter{[2..n+1]};
  Mat1:=NullMat(n+1, n+1);
  for i in [1..n]
  do
    for j in [1..n]
    do
      Mat1[i+1][j+1]:=GramMat[i][j];
    od;
  od;
  eVect:=TheCenterRed*GramMat;
  for i in [1..n]
  do
    Mat1[1][1+i]:=-eVect[i];
    Mat1[1+i][1]:=-eVect[i];
  od;
  eScal:=1 + TheCenterRed*eVect;
  Mat1[1][1]:=eScal;
  MatRet1:=RemoveFractionMatrix(Mat1);
  Mat2:=NullMat(n+1, n+1);
  Mat2[1][1]:=1;
  while(true)
  do
    if IsPositiveDefiniteSymmetricMatrix(MatRet1)=true then
      break;
    fi;
    MatRet1:=MatRet1+Mat2;
  od;
  return [MatRet1, Mat2];
end;




VertexRepresentationDelaunaySymmetry:=function(TheGroup, EXT, eCenter)
  local PermGen, MatrixGen, eMat, eTrans, eBigMat, eList, GRPperm, GRPmat, PhiPermMat, n, RedCenterFirst;
  n:=Length(EXT[1])-1;
  PermGen:=[];
  MatrixGen:=[];
  RedCenterFirst:=eCenter{[2..n+1]};
  for eMat in GeneratorsOfGroup(TheGroup)
  do
    eTrans:=RedCenterFirst-RedCenterFirst*eMat;
    eBigMat:=FuncCreateBigMatrix(eTrans, eMat);
    Add(MatrixGen, eBigMat);
    eList:=List(EXT, x->Position(EXT, x*eBigMat));
    Add(PermGen, PermList(eList));
  od;
  GRPperm:=PersoGroupPerm(PermGen);
  SetSize(GRPperm, Size(TheGroup));
  GRPmat:=PersoGroupMatrix(MatrixGen, n+1);
  PhiPermMat:=GroupHomomorphismByImagesNC(GRPperm, GRPmat, PermGen, MatrixGen);
  return rec(PermutationStabilizer:=GRPperm, PhiPermMat:=PhiPermMat);
end;


Delaney_GetString:=function(ListRet)
  local eStr, iFlag;
  eStr:="";
  for iFlag in [1..Length(ListRet)]
  do
    if iFlag > 1 then
      eStr:=Concatenation(eStr, " ");
    fi;
    eStr:=Concatenation(eStr, String(ListRet[iFlag]));
  od;
  return eStr;
end;

Delaney_GetReducedEList:=function(eList)
  local ListRet, iFlag;
  ListRet:=[];
  for iFlag in [1..Length(eList)]
  do
    if eList[iFlag] >= iFlag then
      Add(ListRet, eList[iFlag]);
    fi;
  od;
  return ListRet;
end;




Delaney_ForDelaneyGetListMIJ:=function(ReducedSigmaPerm, H)
  local nbPerm, nbOrb, ListMIJ, iSig, jSig, ListCycleNr, GRPij, ListStatus, ListRet, iFlag, eO;
  nbPerm:=Length(ReducedSigmaPerm);
  nbOrb:=Length(H[1][2]);
  ListMIJ:=[];
  for iSig in [1..nbPerm-1]
  do
    jSig:=iSig+1;
    ListCycleNr:=H[iSig][jSig];
    GRPij:=Group([ReducedSigmaPerm[iSig], ReducedSigmaPerm[jSig]]);
    ListStatus:=ListWithIdenticalEntries(nbOrb, 0);
    ListRet:=[];
    for iFlag in [1..nbOrb]
    do
      if ListStatus[iFlag]=0 then
        eO:=Orbit(GRPij, iFlag, OnPoints);
        ListStatus{eO}:=ListWithIdenticalEntries(Length(eO), 1);
        Add(ListRet, ListCycleNr[iFlag]);
      fi;
    od;
    Add(ListMIJ, ListRet);
  od;
  return ListMIJ;
end;

Delaney_GetStringSymbol:=function(eDelaneyGAP)
  local eStringRed, iSigma, iSig, ListFlagPerm, nb, ListMIJ;
  nb:=Length(eDelaneyGAP.ListSigmaList)-1;
  eStringRed:=Concatenation(":", String(eDelaneyGAP.nbOrb[1]), " ", String(nb), ":");
  for iSigma in [1..Length(eDelaneyGAP.ListSigmaList)]
  do
    if iSigma>1 then
      eStringRed:=Concatenation(eStringRed, ",");
    fi;
    eStringRed:=Concatenation(eStringRed, Delaney_GetString(Delaney_GetReducedEList(eDelaneyGAP.ListSigmaList[iSigma])));
  od;
  ListFlagPerm:=List(eDelaneyGAP.ListSigmaList, PermList);
  ListMIJ:=Delaney_ForDelaneyGetListMIJ(ListFlagPerm, eDelaneyGAP.Hmatrix);
  eStringRed:=Concatenation(eStringRed, ":");
  for iSig in [1..nb]
  do
    if iSig > 1 then
      eStringRed:=Concatenation(eStringRed, ",");
    fi;
    eStringRed:=Concatenation(eStringRed, Delaney_GetString(ListMIJ[iSig]));
  od;
  eStringRed:=Concatenation(eStringRed, ">");
  return eStringRed;
end;


Delaney_DualHmatrix:=function(Hmat)
  local n, RevHmat, i, j, iRev, jRev;
  n:=Length(Hmat);
  RevHmat:=NullMat(n,n);
  for i in [1..n-1]
  do
    for j in [i+1..n]
    do
      iRev:=n+1-i;
      jRev:=n+1-j;
      RevHmat[jRev][iRev]:=Hmat[i][j];
    od;
  od;
  return RevHmat;
end;


DelaunayTesselation_DelaneySymbol:=function(DataLattice, DelaunayDatabase)
  local n, ListOrbitFlag, ListFAC, IsComputedListOrbitFlag, ComputeListOrbitFlags, GetListOrbitFlag, DoFlagDisplacement, FlagFindEquivalence, FindFlagEquivalenceRepr, GetDelaneySymbol;
  IsComputedListOrbitFlag:=false;
  n:=DataLattice.n;
  ComputeListOrbitFlags:=function()
    local nbOrb, iOrb, TheStab, TheStabPerm, EXT, ListAdj, eRecFlag, eOrbFlag, FAC, ListIneq, LOrbFlag, O, eOrb;
    if IsComputedListOrbitFlag=true then
      return;
    fi;
    nbOrb:=DelaunayDatabase.FuncDelaunayGetNumber();
    ListOrbitFlag:=[];
    ListFAC:=[];
    for iOrb in [1..nbOrb]
    do
      TheStab:=DelaunayDatabase.FuncDelaunayGetGroup(iOrb);
      TheStabPerm:=TheStab.PermutationStabilizer;
      EXT:=DelaunayDatabase.FuncDelaunayGetEXT(iOrb);
      ListAdj:=DelaunayDatabase.FuncDelaunayGetAdjacencies(iOrb);
      FAC:=[];
      for eOrb in ListAdj
      do
        O:=Orbit(TheStabPerm, eOrb.eInc, OnSets);
        ListIneq:=List(O, x->FindFacetInequality(EXT, x));
        Append(FAC, ListIneq);
      od;
      Print("iOrb=", iOrb, " |EXT|=", Length(EXT), " |FAC|=", Length(FAC), " |GRP|=", Order(TheStabPerm), "\n");
      Add(ListFAC, FAC);
      LOrbFlag:=ListFlagOrbit(TheStabPerm, EXT, FAC);
      for eOrbFlag in LOrbFlag
      do
        eRecFlag:=rec(iOrb:=iOrb, eBigMat:=IdentityMat(n+1), eFlagEXT:=eOrbFlag);
        Add(ListOrbitFlag, eRecFlag);
      od;
    od;
    IsComputedListOrbitFlag:=true;
  end;
  GetListOrbitFlag:=function()
    ComputeListOrbitFlags();
    return ListOrbitFlag;
  end;
  DoFlagDisplacement:=function(eRecFlag, i)
    local iOrb, eFlagEXT, EXT, fFlagEXT, eFacInc, ListAdj, TheStab, TheStabPerm, eOrb, eEquivMatr, eEquivPerm, jOrb, EXTj, EXTimageJ, fList, eNewBigMat, eInc, EXTimageI;
    eFlagEXT:=eRecFlag.eFlagEXT;
    EXT:=DelaunayDatabase.FuncDelaunayGetEXT(eRecFlag.iOrb);
    if i<n then
      iOrb:=eRecFlag.iOrb;
      fFlagEXT:=FlagDisplacement(eFlagEXT, EXT, ListFAC[iOrb], i+1);
      return rec(iOrb:=iOrb, eBigMat:=eRecFlag.eBigMat, eFlagEXT:=fFlagEXT);
    fi;
    eFacInc:=eFlagEXT[n];
    ListAdj:=DelaunayDatabase.FuncDelaunayGetAdjacencies(eRecFlag.iOrb);
    TheStab:=DelaunayDatabase.FuncDelaunayGetGroup(eRecFlag.iOrb);
    TheStabPerm:=TheStab.PermutationStabilizer;
    for eOrb in ListAdj
    do
      eEquivPerm:=RepresentativeAction(TheStabPerm, eOrb.eInc, eFacInc, OnSets);
      if eEquivPerm<>fail then
        eEquivMatr:=Image(TheStab.PhiPermMat, eEquivPerm);
        jOrb:=eOrb.iDelaunay;
        EXTj:=DelaunayDatabase.FuncDelaunayGetEXT(jOrb);
        EXTimageI:=EXT*eRecFlag.eBigMat;
        eNewBigMat:=eOrb.eBigMat*eEquivMatr*eRecFlag.eBigMat;
        EXTimageJ:=EXTj*eNewBigMat;
        fFlagEXT:=[];
        for eInc in eFlagEXT
        do
          fList:=List(EXTimageI{eInc}, x->Position(EXTimageJ, x));
          Add(fFlagEXT, Set(fList));
        od;
        return rec(iOrb:=jOrb, eBigMat:=eNewBigMat, eFlagEXT:=fFlagEXT);
      fi;
    od;
    Error("We should never reach that stage");
  end;
  FlagFindEquivalence:=function(eRecFlag, fRecFlag)
    local iOrb, TheStab, TheStabPerm, eEquivPerm, eEquivMatr;
    if eRecFlag.iOrb<>fRecFlag.iOrb then
      return fail;
    fi;
    iOrb:=eRecFlag.iOrb;
    TheStab:=DelaunayDatabase.FuncDelaunayGetGroup(iOrb);
    TheStabPerm:=TheStab.PermutationStabilizer;
    eEquivPerm:=OnTuplesSetsRepresentativeAction(TheStabPerm, eRecFlag.eFlagEXT, fRecFlag.eFlagEXT);
    if eEquivPerm=fail then
      return fail;
    fi;
    eEquivMatr:=Image(TheStab.PhiPermMat, eEquivPerm);
    return Inverse(eRecFlag.eBigMat)*eEquivMatr*fRecFlag.eBigMat;
  end;
  FindFlagEquivalenceRepr:=function(eRecFlag)
    local iFlag, test;
    for iFlag in [1..Length(ListOrbitFlag)]
    do
      test:=FlagFindEquivalence(ListOrbitFlag[iFlag], eRecFlag);
      if test<>fail then
        return rec(iFlag:=iFlag, eBigMat:=test);
      fi;
    od;
    Error("We should never reach that stage B");
  end;
  GetDelaneySymbol:=function()
    local nbOrbFlag, ListSigmaList, i, j, eList, eRecFlag, fRecFlag, eListMIJ, iFlag, gRecFlag, siz, eInfo, m, eDelaneyGAPdual, eDelaneyGAP, eString, eStringDual, Hmatrix;
    ComputeListOrbitFlags();
    nbOrbFlag:=Length(ListOrbitFlag);
    ListSigmaList:=[];
    for i in [0..n]
    do
      eList:=[];
      for eRecFlag in ListOrbitFlag
      do
        fRecFlag:=DoFlagDisplacement(eRecFlag, i);
        Add(eList, FindFlagEquivalenceRepr(fRecFlag).iFlag);
      od;
#      Print("i=", i, " eList=", eList, " ePerm=", PermList(eList), "\n");
      Add(ListSigmaList, eList);
    od;
    Hmatrix:=NullMat(n + 1, n + 1);
    for i in [0..n-1]
    do
      for j in [i+1..n]
      do
        eListMIJ:=[];
        for iFlag in [1..nbOrbFlag]
        do
          eRecFlag:=ListOrbitFlag[iFlag];
          siz:=0;
          while(true)
          do
            fRecFlag:=DoFlagDisplacement(eRecFlag, i);
            gRecFlag:=DoFlagDisplacement(fRecFlag, j);
            eInfo:=FindFlagEquivalenceRepr(gRecFlag);
            siz:=siz+1;
            if eInfo.iFlag=iFlag then
              break;
            fi;
            eRecFlag:=gRecFlag;
          od;
          m:=Order(eInfo.eBigMat)*siz;
          Add(eListMIJ, m);
        od;
#        Print("i=", i, " j=", j, " eListMIJ=", eListMIJ, "\n");
        Hmatrix[i+1][j+1]:=eListMIJ;
        Hmatrix[j+1][i+1]:=eListMIJ;
      od;
    od;
    eDelaneyGAP:=rec(nbOrb:=[nbOrbFlag,n], ListSigmaList:=ListSigmaList, Hmatrix:=Hmatrix);
    eDelaneyGAPdual:=rec(nbOrb:=[nbOrbFlag,n], ListSigmaList:=Reversed(ListSigmaList), Hmatrix:=Delaney_DualHmatrix(Hmatrix));
    eString:=Delaney_GetStringSymbol(eDelaneyGAP);
    eStringDual:=Delaney_GetStringSymbol(eDelaneyGAPdual);
    return rec(eDelaneyGAP:=eDelaneyGAP,
               eDelaneyGAPdual:=eDelaneyGAPdual,
               eString:=eString,
               eStringDual:=eStringDual);
  end;
  return rec(GetListOrbitFlag:=GetListOrbitFlag,
             DoFlagDisplacement:=DoFlagDisplacement,
             FlagFindEquivalence:=FlagFindEquivalence,
             FindFlagEquivalenceRepr:=FindFlagEquivalenceRepr,
             GetDelaneySymbol:=GetDelaneySymbol);
end;




DelaunayTesselation_GetOrbitCells:=function(DataLattice, DelaunayDatabase)
  local n, ListOrbitByDimension, i, nbOrb, iOrb, TheStab, EXT, ListMatrGen, ePermGen, eMatr, GRPmatr, eRec, ListOrbit, ListPerm, eGen, eList, ePerm, GRPperm, LOrb, eOrb, FuncInsert, EXTfacet;
  n:=DataLattice.n;
  ListOrbitByDimension:=[];
  for i in [0..n]
  do
    Add(ListOrbitByDimension, []);
  od;
  nbOrb:=DelaunayDatabase.FuncDelaunayGetNumber();
  for iOrb in [1..nbOrb]
  do
    Print("iOrb=", iOrb,  " / ", nbOrb, "\n");
    TheStab:=DelaunayDatabase.FuncDelaunayGetGroup(iOrb);
    EXT:=DelaunayDatabase.FuncDelaunayGetEXT(iOrb);
    ListMatrGen:=[];
    for ePermGen in GeneratorsOfGroup(TheStab.PermutationStabilizer)
    do
      eMatr:=FindTransformation(EXT, EXT, ePermGen);
      Add(ListMatrGen, eMatr);
    od;
    GRPmatr:=Group(ListMatrGen);
    eRec:=rec(EXT:=EXT, TheStab:=GRPmatr);
    Add(ListOrbitByDimension[n+1], eRec);
  od;
  for i in Reversed([1..n])
  do
    Print("i=", i, " / ", n, "\n");
    ListOrbit:=[];
    FuncInsert:=function(EXT)
      local eIso, eOrbit, eIsoB, test, eRec;
      eIso:=Isobarycenter(EXT);
      for eOrbit in ListOrbit
      do
        eIsoB:=Isobarycenter(eOrbit.EXT);
        test:=DataLattice.FuncEquiv(EXT, eOrbit.EXT, eIso, eIsoB);
        if test<>false then
          return;
        fi;
      od;
      TheStab:=DataLattice.FuncAutom(EXT, eIso);
      eRec:=rec(EXT:=EXT, TheStab:=TheStab);
      Add(ListOrbit, eRec);
    end;
    for eRec in ListOrbitByDimension[i+1]
    do
      ListPerm:=[];
      for eGen in GeneratorsOfGroup(eRec.TheStab)
      do
        eList:=List(eRec.EXT, x->Position(eRec.EXT, x*eGen));
        ePerm:=PermList(eList);
        Add(ListPerm, ePerm);
      od;
      GRPperm:=Group(ListPerm);
      Print("  |EXT|=", Length(eRec.EXT), " |G|=", Order(GRPperm), "\n");
      LOrb:=DualDescriptionStandard(eRec.EXT, GRPperm);
      for eOrb in LOrb
      do
        EXTfacet:=eRec.EXT{eOrb};
        FuncInsert(EXTfacet);
      od;
    od;
    ListOrbitByDimension[i]:=ListOrbit;
  od;
  Print("ListNr=", List(ListOrbitByDimension, Length), "\n");
  return ListOrbitByDimension;
end;







#
# we return a basis of vectors for isomorphy/automorphy computation
# whether it is isomorphy or automorphy is very important because
# it determines if we can be selective in choosing vectors or not.
FuncMethod6_SVR:=function(GramMat, InvariantBasis, AffBas, EXT, typecall, NeedAffBas)
  local n, SVR, eEXT, ReturnAffBas, Vcent, EXTwork, reply, ListStatus, GetInfo, ListChar, ListSizes, nbEnt, SVRappend, ListZero, ListSizesSel, SVRtest, DiscInvTest, pos, idx, SVR_EXT, DiscInv, ExtendedInvariantBasis, MinSize, ListApp, ListColl, GetPairInv, ListAppSma, ListPos, WeAppend, FamInfo, ListSelect, eSetSelect, CriticalLevelForNauty, eStart, FileSave, SVRshortened, FuncCanonicalizeVector, DiscriminantMatrix, CharPair, CP, TheCenter;
  n:=Length(GramMat);
  CP:=CenterRadiusDelaunayPolytopeGeneral(GramMat, EXT);
  TheCenter:=CP.Center;
  CharPair:=CharacterizingPair(GramMat, TheCenter);
  DiscriminantMatrix:=CharPair[1];
  if Length(InvariantBasis)=0 then
    return rec(SVR:=[], AffBas:=IdentityMat(Length(EXT[1])));
  fi;
  if IsIntegralMat(EXT)=true then
    EXTwork:=EXT;
  else
    Vcent:=TheCenter{[2..n+1]};
    reply:=CVPVallentinProgram(GramMat, Vcent);
    EXTwork:=List(reply.ListVect, x->Concatenation([1], x));
  fi;
  SVR_EXT:=[];
  Append(SVR_EXT, EXTwork);
  Append(SVR_EXT, -EXTwork);
  ExtendedInvariantBasis:=List(InvariantBasis, x->Concatenation([0],x));
  # that optimization might be useful sometimes
  CriticalLevelForNauty:=1000;
  FuncCanonicalizeVector:=function(eVect)
    local pos, eSign;
    pos:=First([1..Length(eVect)], x->eVect[x]<>0);
    if eVect[pos]>0 then
      eSign:=1;
    else
      eSign:=-1;
    fi;
    return eSign*eVect;
  end;
  if IsIntegralMat(EXT)=true then
    if RankMat(EXT)=Length(EXT[1]) and AbsInt(DeterminantMat(BaseIntMat(EXT)))=1 then
      return rec(SVR:=SVR_EXT, AffBas:=CreateAffineBasis(EXT));
    fi;
    GetInfo:=function(eVect)
      local eProd, ListScal;
      eProd:=eVect*DiscriminantMatrix;
      ListScal:=List(SVR_EXT, x->x*eProd);
      return Collected(ListScal);
    end;
    FamInfo:=GetCollectedList(ExtendedInvariantBasis, GetInfo);
#    Print("ListSizes=", FamInfo.ListSizes, "\n");
    nbEnt:=Length(FamInfo.ListSizes);
    ListStatus:=ListWithIdenticalEntries(nbEnt, 0);
    ListSelect:=ListWithIdenticalEntries(nbEnt, 0);
    SVRappend:=[];
    GetPairInv:=function(SVR)
      local SVR_BaseInt, SNF, TheDet, rnk, i;
      SVR_BaseInt:=BaseIntMat(SVR);
      SNF:=SmithNormalFormIntegerMat(SVR_BaseInt);
      TheDet:=1;
      rnk:=Length(SVR_BaseInt);
      for i in [1..rnk]
      do
        TheDet:=TheDet*SNF[i][i];
      od;
      return rec(TheDet:=TheDet, TheRank:=rnk);
    end;
    while(true)
    do
      SVR:=Concatenation(SVR_EXT, SVRappend);
      DiscInv:=GetPairInv(SVR);
      WeAppend:=false;
      if DiscInv.TheDet=1 and DiscInv.TheRank=n+1 then
        if NeedAffBas=true and Length(SVR)>CriticalLevelForNauty then
          WeAppend:=true;
          SVRshortened:=Set(List(SVR, FuncCanonicalizeVector));
          eStart:=GetStartingAffine(SVRshortened);
          ReturnAffBas:=ExtendToCompleteAffineBasis(SVRshortened, eStart);
          if ReturnAffBas<>false then
            break;
          fi;
        else
          ReturnAffBas:="irrelevant";
          break;
        fi;
      fi;
      ListZero:=Filtered([1..nbEnt], x->ListStatus[x]=0);
      ListSizesSel:=FamInfo.ListSizes{ListZero};
      MinSize:=Minimum(ListSizesSel);
      if typecall="automorphy" then
        pos:=Position(ListSizesSel, MinSize);
        idx:=ListZero[pos];
        ListApp:=FamInfo.ListOcc[idx];
        ListStatus[idx]:=1;
        eSetSelect:=[idx];
      elif typecall="isomorphy" then
        ListPos:=Filtered([1..Length(ListSizesSel)], x->ListSizesSel[x]=MinSize);
        ListApp:=[];
        for pos in ListPos
        do
          idx:=ListZero[pos];
          ListAppSma:=FamInfo.ListOcc[idx];
          ListStatus[idx]:=1;
          ListApp:=Concatenation(ListApp, ListAppSma);
        od;
        eSetSelect:=ShallowCopy(ListPos);
      else
        Error("Wrong type call option");
      fi;
      if WeAppend=false then
        SVRtest:=Concatenation(SVR_EXT, SVRappend, ExtendedInvariantBasis{ListApp});
        DiscInvTest:=GetPairInv(SVRtest);
        if DiscInvTest.TheDet < DiscInv.TheDet or DiscInvTest.TheRank > DiscInv.TheRank then
          WeAppend:=true;
        fi;
      fi;
      if WeAppend=true then
        Append(SVRappend, ExtendedInvariantBasis{ListApp});
#        Print("Now |SVRappend|=", Length(SVRappend), " det=", DiscInvTest.TheDet, " rank=", DiscInvTest.TheRank, "\n");
        ListSelect{eSetSelect}:=ListWithIdenticalEntries(Length(eSetSelect), 1);
      fi;
    od;
    return rec(SVR:=SVR, AffBas:=ReturnAffBas);
  fi;
  if NeedAffBas=true then
    ReturnAffBas:=Concatenation(List(AffBas, x->Concatenation([0],x)), EXT[1]);
  else
    ReturnAffBas:="irrelevant";
  fi;
  return rec(SVR:=SVR_EXT, AffBas:=ReturnAffBas);
end;

SimpleGetInvariantFamily:=function(GramMat, InvariantBasis, EXT)
  local typecall, NeedAffBas, AffBas;
  typecall:="isomorphy";
  NeedAffBas:=false;
  AffBas:="irrelevant";
  return FuncMethod6_SVR(GramMat, InvariantBasis, AffBas, EXT, typecall, NeedAffBas).SVR;
end;






# The basic method, efficient when the orbit is small
# uses only the center
Stabilizer_Method2:=function(DataLattice, ThePoint)
  local n, RedPointFirst, RedPointSecond, FuncActionMod1, PermStab, GRP;
  n:=DataLattice.n;
  RedPointFirst:=ThePoint{[2..n+1]};
  RedPointSecond:=VectorMod1(RedPointFirst);
  FuncActionMod1:=function(eClass, eElt)
    return VectorMod1(eClass*Image(DataLattice.phi, eElt));
  end;
  PermStab:=Stabilizer(DataLattice.PermGRP, RedPointSecond, FuncActionMod1);
  GRP:=Image(DataLattice.phi, PermStab);
  SetSize(GRP, Order(PermStab));
  return GRP;
end;




# this methods uses only the center
Stabilizer_Method3:=function(DataLattice, ThePoint)
  local n, RedPointFirst, Stab, i, eList, OneDen, OnClassesModPW, RedPointPW, TheOrd, eComp, GRP;
  n:=DataLattice.n;
  RedPointFirst:=ThePoint{[2..n+1]};
  eList:=FactorsInt(ListFactors(ThePoint));
  Stab:=ShallowCopy(DataLattice.PermGRP);
  TheOrd:=Size(DataLattice.PointGRP);
  for i in [1..Length(eList)]
  do
    OneDen:=Product(eList{[i+1..Length(eList)]});
    OnClassesModPW:=function(eClass, eGen)
      return VectorModPW(eClass*Image(DataLattice.phi, eGen), OneDen);
    end;
    RedPointPW:=VectorModPW(RedPointFirst, OneDen);
    eComp:=OrbitStabilizer(Stab, RedPointPW, OnClassesModPW);
    Stab:=eComp.stabilizer;
    TheOrd:=TheOrd/Length(eComp.orbit);
    Stab:=Group(SmallGeneratingSet(Stab));
    Print("Den=", OneDen, "  |Stab|=", TheOrd, "  nbGen=", Length(GeneratorsOfGroup(Stab)), "\n");
  od;
  GRP:=Image(DataLattice.phi, Stab);
  SetSize(GRP, TheOrd);
  return GRP;
end;





# this method uses the vertices of the Delaunay
Stabilizer_Method4:=function(DataLattice, EXT, GRP)
  local eElt, eBigMat, RedMat, ListPermGens, ListMatrGens, ThePermGrp, TheMatrGrp, FuncInsert;
  ListPermGens:=[];
  ThePermGrp:=Group(());
  ListMatrGens:=[];
  FuncInsert:=function(eElt, RedMat)
    if not(eElt in ThePermGrp) then
      Add(ListPermGens, eElt);
      ThePermGrp:=Group(ListPermGens);
      Add(ListMatrGens, RedMat);
    fi;
  end;
  for eElt in GRP
  do
    eBigMat:=FindTransformation(EXT, EXT, eElt);
    if DataLattice.TestBelonging(eBigMat)=true then
      RedMat:=FuncExplodeBigMatrix(eBigMat).MatrixTransformation;
      FuncInsert(eElt, RedMat);
    fi;
  od;
  TheMatrGrp:=PersoGroupMatrix(ListMatrGens, DataLattice.n);
  SetSize(TheMatrGrp, Order(ThePermGrp));
  return TheMatrGrp;
end;

Stabilizer_Method7:=function(DataLattice, EXT, GRP)
  return KernelLinPolytopeIntegral_Automorphism_Subspaces(EXT, GRP).GRPmatr;
end;


GetScalMat_Method8:=function(DataLattice, EXT)
  local SVR_EXT, EXText, CP, TheCenter, CharPair, nbV, ScalMat, i, j, eScal;
  SVR_EXT:=List(DataLattice.InvariantBase, x->Concatenation([0],x));
  EXText:=Concatenation(EXT, SVR_EXT);
  CP:=CenterRadiusDelaunayPolytopeGeneral(DataLattice.GramMat, EXT);
  TheCenter:=CP.Center;
  CharPair:=CharacterizingPair(DataLattice.GramMat, TheCenter);
  return rec(Qmat:=CharPair[1], EXText:=EXText);
end;

Stabilizer_Method8:=function(DataLattice, EXT)
  local GRPbig, GRP, GRPfinal, ListGen, GRPred, RecMat;
  RecMat:=GetScalMat_Method8(DataLattice, EXT);
  GRPbig:=LinPolytope_Automorphism_GramMat(RecMat.EXText, RecMat.Qmat);
  Print("|GRPbig| = ", Order(GRPbig), "\n");
  GRP:=SecondReduceGroupAction(GRPbig, [1..Length(EXT)]);
  Print("|GRP| = ", Order(GRP), "\n");
  GRPfinal:=KernelLinPolytopeIntegral_Automorphism_Subspaces(EXT, GRP).GRPmatr;
  Print("|GRPfinal| = ", Order(GRPfinal), "\n");
  ListGen:=List(GeneratorsOfGroup(GRPfinal), x->FuncExplodeBigMatrix(x).MatrixTransformation);
  GRPred:=PersoGroupMatrix(ListGen, DataLattice.n);
  SetSize(GRPred, Order(GRPfinal));
  Print("|GRPred| = ", Order(GRPred), "\n");
  return GRPred;
end;




M6_Stabilizer:=function(GramMat, InvariantBase, AffBas, FuncLatticeAutomorphism, EXT, TheCenter, NeedAffBas)
  local CharPair, VectorKey, TheMatrGrp, ListGens, eBigMat, GRP;
  CharPair:=CharacterizingPair(GramMat, TheCenter);
  VectorKey:=FuncMethod6_SVR(GramMat, InvariantBase, AffBas, EXT, "automorphy", NeedAffBas);
  ListGens:=[];
  TheMatrGrp:=FuncLatticeAutomorphism(CharPair, VectorKey.SVR, VectorKey.AffBas);
  for eBigMat in GeneratorsOfGroup(TheMatrGrp)
  do
    if eBigMat[1][1]=-1 then
      Add(ListGens, -eBigMat);
    else
      Add(ListGens, eBigMat);
    fi;
  od;
  GRP:=Group(ListGens);
  SetSize(GRP, Size(TheMatrGrp)/2);
  return GRP;
end;


# this methods uses the center only but works only for the natural group.
# the set EXT has to be non-empty and left invariant by automorphism
# preserving TheCenter
Stabilizer_Method6:=function(DataLattice, EXT, TheCenter)
  local TheMatrGrp, ListGens, eBigMat, RedMat, GRP;
  TheMatrGrp:=M6_Stabilizer(DataLattice.GramMat, DataLattice.InvariantBase, DataLattice.AffBas, DataLattice.FuncLatticeAutomorphism, EXT, TheCenter, DataLattice.NeedAffBas);
  ListGens:=[];
  for eBigMat in GeneratorsOfGroup(TheMatrGrp)
  do
    RedMat:=FuncExplodeBigMatrix(eBigMat).MatrixTransformation;
    Add(ListGens, RedMat);
  od;
  GRP:=Group(ListGens);
  SetSize(GRP, Size(TheMatrGrp));
  return GRP;
end;





# this methods works only if the isometry group is equal to the
# full symmetry group of the Delaunay. When it works it is
# systematically the fastest.
Stabilizer_Method0:=function(DataLattice, EXT, GRP)
  local ListGen, eGen, eBigMat, GRPreturn;
  ListGen:=[];
  for eGen in GeneratorsOfGroup(GRP)
  do
    eBigMat:=FindTransformation(EXT, EXT, eGen);
    if DataLattice.TestBelonging(eBigMat)=false then
      return fail;
    fi;
    Add(ListGen, FuncExplodeBigMatrix(eBigMat).MatrixTransformation);
  od;
  if Length(ListGen)=0 then
    GRPreturn:=Group([IdentityMat(DataLattice.n)]);
    SetSize(GRPreturn, 1);
  else
    GRPreturn:=Group(ListGen);
    SetSize(GRPreturn, Size(GRP));
  fi;
  return GRPreturn;
end;



StabilizerOfDelaunay:=function(DataLattice, EXT)
  local CP, TheCenter, n, DM, GRP, EasyCase, REP, TheReply, LFactors, HLR, LimitEfficiencyNauty;
  TheCenter:=Isobarycenter(EXT);
  LimitEfficiencyNauty:=2000;
  if Length(EXT)<LimitEfficiencyNauty then
    DM:=DistanceMatrixDelaunay(DataLattice.GramMat, EXT);
    GRP:=AutomorphismGroupEdgeColoredGraph(DM);
  else
    GRP:="we decided not to compute it";
  fi;
  if IsVectorRational(TheCenter)=true then
    LFactors:=FactorsInt(ListFactors(TheCenter));
  else
    LFactors:="undefined";
  fi;
  if Length(EXT)<LimitEfficiencyNauty then
    REP:=Stabilizer_Method0(DataLattice, EXT, GRP);
  else
    REP:=fail;
  fi;
  if REP<>fail then
    EasyCase:=true;
    TheReply:=REP;
  else
    EasyCase:=false;
    if Length(EXT)<LimitEfficiencyNauty then
      if DataLattice.n <= 10 then
        TheReply:=Stabilizer_Method2(DataLattice, TheCenter);
      elif Order(GRP) < 50000 then
        TheReply:=Stabilizer_Method4(DataLattice, EXT, GRP);
      elif LFactors<>"undefined" and Length(LFactors) > 2 then
        TheReply:=Stabilizer_Method3(DataLattice, TheCenter);
      else
        TheReply:=Stabilizer_Method6(DataLattice, EXT, TheCenter);
      fi;
    else
      if DataLattice.n <= 10 then
        TheReply:=Stabilizer_Method2(DataLattice, TheCenter);
      elif LFactors<>"undefined" and Length(LFactors) > 2 then
        TheReply:=Stabilizer_Method3(DataLattice, TheCenter);
      else
        TheReply:=Stabilizer_Method6(DataLattice, EXT, TheCenter);
      fi;
    fi;
  fi;
  HLR:=VertexRepresentationDelaunaySymmetry(TheReply, EXT, TheCenter);
  return rec(PrivateInfo:=rec(EasyCase:=EasyCase, GRP:=GRP),
             PermutationStabilizer:=HLR.PermutationStabilizer,
             PhiPermMat:=HLR.PhiPermMat);
end;







# the basic method, the fastest, when it works.
Equivalence_Method0:=function(DataLattice, EXT1, EXT2, Delaunay1Stab, ePerm)
  local eBigMat;
  eBigMat:=FindTransformation(EXT1, EXT2, ePerm);
  if DataLattice.TestBelonging(eBigMat)=true then
    return eBigMat;
  fi;
  if Delaunay1Stab.PrivateInfo.EasyCase=true then
    return false;
  else
    return fail;
  fi;
end;



# this method is inspired from a method proposed by A. Hulpke for
# computing intersection of groups with right cosets.
Equivalence_Method1:=function(DataLattice, EXT1, EXT2, Delaunay1Stab, ePerm)
  local eBigMat, TheBaryCenter1, TheBaryCenter2, n, RedCenterFirst1, RedCenterFirst2, RedMat, eImage, test, HypDim, FuncTestBelongingMetStabDelaunay1, eTrans;
  eBigMat:=FindTransformation(EXT1, EXT2, ePerm);
  TheBaryCenter1:=Sum(EXT1)/Length(EXT1);
  TheBaryCenter2:=Sum(EXT2)/Length(EXT2);
  n:=DataLattice.n;
  RedCenterFirst1:=TheBaryCenter1{[2..n+1]};
  RedCenterFirst2:=TheBaryCenter2{[2..n+1]};
  if DataLattice.TestBelonging(eBigMat)=true then
    return eBigMat;
  fi;
  RedMat:=FuncExplodeBigMatrix(eBigMat).MatrixTransformation;
  HypDim:=Length(EXT1[1]);
  FuncTestBelongingMetStabDelaunay1:=function(eMat)
    local iExt, jExt, Vvector, Vred, Vimg, dist1, dist2;
    for iExt in [1..Length(EXT1)-1]
    do
      for jExt in [iExt+1..Length(EXT1)]
      do
        Vvector:=EXT1[iExt]-EXT1[jExt];
        Vred:=Vvector{[2..HypDim]};
        dist1:=Vred*DataLattice.GramMat*Vred;
        #
        Vimg:=Vred*eMat;
        dist2:=Vimg*DataLattice.GramMat*Vimg;
        if dist1<>dist2 then
          return false;
        fi;
      od;
    od;
    return true;
  end;
  eImage:=Image(Delaunay1Stab.PhiPermMat);
  test:=First(RightTransversal(DataLattice.PointGRP, eImage), y->FuncTestBelongingMetStabDelaunay1(y*RedMat));
  if test=0 then
    return false;
  else
    eTrans:=RedCenterFirst1-RedCenterFirst2*test;
    return FuncCreateBigMatrix(eTrans, test);
  fi;
end;




# the basic method without optimization, efficient when the
# orbit of Delaunay is small
# it uses only the centers.
Equivalence_Method2:=function(DataLattice, ThePoint1, ThePoint2)
  local n, RedPointFirst1, RedPointFirst2, RedPointSecond1, RedPointSecond2, FuncActionMod1, eGen, eMat, eTrans;
  n:=DataLattice.n;
  RedPointFirst1:=ThePoint1{[2..n+1]};
  RedPointFirst2:=ThePoint2{[2..n+1]};
  RedPointSecond1:=VectorMod1(RedPointFirst1);
  RedPointSecond2:=VectorMod1(RedPointFirst2);
  FuncActionMod1:=function(eClass, eGen)
    return VectorMod1(eClass*Image(DataLattice.phi, eGen));
  end;
  eGen:=RepresentativeAction(DataLattice.PermGRP, RedPointSecond1, RedPointSecond2, FuncActionMod1);
  if eGen<>fail then
    eMat:=Image(DataLattice.phi, eGen);
    eTrans:=RedPointFirst2-RedPointFirst1*eMat;
    return FuncCreateBigMatrix(eTrans, eMat);
  fi;
  return false;
end;







# an improvement over method2, a method that use a sequence
# of stabilizer,
# It uses only the centers.
Equivalence_Method3:=function(DataLattice, ThePoint1, ThePoint2)
  local n, RedPointFirst1, RedPointFirst2, RedPointSecond1, RedPointSecond2, GrpStab, TheDen1, TheDen2, i, eList, OneDen, OnClassesModPW, RedPointPW1, RedPointPW2, RedPointSecondPrev1, eMat, eTrans, eMatSearch, eGen, LFactors1, eBigMat, RedPointForStab;
  Print("Begin of Equivalence_Method3\n");
  n:=DataLattice.n;
  RedPointFirst1:=ThePoint1{[2..n+1]};
  RedPointFirst2:=ThePoint2{[2..n+1]};
  RedPointSecond1:=VectorMod1(RedPointFirst1);
  RedPointSecond2:=VectorMod1(RedPointFirst2);
  #
  RedPointSecondPrev1:=ShallowCopy(RedPointSecond1);
  GrpStab:=ShallowCopy(DataLattice.PermGRP);
  eMatSearch:=IdentityMat(n);
  LFactors1:=FactorsInt(ListFactors(ThePoint1));
  for i in [1..Length(LFactors1)]
  do
    OneDen:=Product(LFactors1{[i+1..Length(LFactors1)]});
    OnClassesModPW:=function(eClass, g)
      return VectorModPW(eClass*Image(DataLattice.phi, g), OneDen);
    end;
    RedPointPW1:=VectorModPW(RedPointSecondPrev1, OneDen);
    RedPointPW2:=VectorModPW(RedPointSecond2, OneDen);
    eGen:=RepresentativeAction(GrpStab, RedPointPW1, RedPointPW2, OnClassesModPW);
    if eGen=fail then
      return false;
    fi;
    eMat:=Image(DataLattice.phi, eGen);
    eMatSearch:=eMatSearch*eMat;
    RedPointSecondPrev1:=OnClassesMod1(RedPointSecondPrev1, eMat);
    if RedPointSecondPrev1=RedPointSecond2 then
      eTrans:=RedPointFirst2-RedPointFirst1*eMatSearch;
      eBigMat:=FuncCreateBigMatrix(eTrans, eMatSearch);
      if ThePoint1*eBigMat<>ThePoint2 then
        Error("We have something to debug here");
      fi;
      return eBigMat;
    fi;
    RedPointForStab:=VectorModPW(RedPointSecondPrev1, OneDen);
    if OnClassesModPW(RedPointForStab, Identity(GrpStab))<>RedPointForStab then
      Error("Inconsistency in stabilizer call");
    fi;
    GrpStab:=Stabilizer(GrpStab, RedPointForStab, OnClassesModPW);
    GrpStab:=Group(SmallGeneratingSet(GrpStab));
#    Print("Den=", OneDen, "  nbGen=", Length(GeneratorsOfGroup(GrpStab)), "\n");
  od;
end;








# efficient when the isometry group is small
Equivalence_Method4:=function(DataLattice, EXT1, EXT2, GRP1, ePerm)
  local eElt, eBigMat;
  for eElt in GRP1
  do
    eBigMat:=FindTransformation(EXT1, EXT2, eElt*ePerm);
    if DataLattice.TestBelonging(eBigMat)=true then
      return eBigMat;
    fi;
  od;
  return false;
end;


# Adapted from LinPolytopeIntegral_Isomorphism_Subspaces
Equivalence_Method7:=function(DataLattice, EXT1, EXT2, GRP1, ePerm)
  local ListGen2, eGen1, eGen2, GRP2;
  ListGen2:=[];
  for eGen1 in GeneratorsOfGroup(GRP1)
  do
    eGen2:=Inverse(ePerm)*eGen1*ePerm;
    Add(ListGen2, eGen2);
  od;
  GRP2:=Group(ListGen2);
  return KernelLinPolytopeIntegral_Isomorphism_Subspaces(EXT1, EXT2, GRP2, ePerm);
end;


Equivalence_Method8:=function(DataLattice, EXT1, EXT2)
  local test, GRPbig2, GRP2, ePerm, RecMat1, RecMat2;
  RecMat1:=GetScalMat_Method8(DataLattice, EXT1);
  RecMat2:=GetScalMat_Method8(DataLattice, EXT2);
  test:=LinPolytope_Isomorphism_GramMat(RecMat1.EXText, RecMat1.Qmat, RecMat2.EXText, RecMat2.Qmat);
  Print("We have test\n");
  if test=false then
    return false;
  fi;
  #
  GRPbig2:=LinPolytope_Automorphism_GramMat(RecMat2.EXText, RecMat2.Qmat);
  Print("We have GRPbig2\n");
  GRP2:=SecondReduceGroupAction(GRPbig2, [1..Length(EXT2)]);
  Print("We have GRP2\n");
  ePerm:=PermList(List([1..Length(EXT2)], x->OnPoints(x, test)));
  Print("We have ePerm\n");
  return KernelLinPolytopeIntegral_Isomorphism_Subspaces(EXT1, EXT2, GRP2, ePerm);
end;





# efficient when the index of the lattice group is small in the
# isometry group
Equivalence_Method5:=function(DataLattice, EXT1, EXT2, Delaunay1Stab, ePerm)
  local u, eBigMat;
  for u in RightCosetsNC(Delaunay1Stab.PrivateInfo.GRP, Delaunay1Stab.PermutationStabilizer)
  do
    eBigMat:=FindTransformation(EXT1, EXT2, Representative(u)*ePerm);
    if DataLattice.TestBelonging(eBigMat)=true then
      return eBigMat;
    fi;
  od;
  return false;
end;



M6_Equivalence:=function(GramMat, InvariantBase, AffBas, FuncLatticeIsomorphism, EXT1, EXT2, TheCenter1, TheCenter2, NeedAffBas)
  local CharPair1, CharPair2, VectorKey1, VectorKey2, U, RetMat;
  if Length(EXT1)<>Length(EXT2) then
    return false;
  fi;
  CharPair1:=CharacterizingPair(GramMat, TheCenter1);
  CharPair2:=CharacterizingPair(GramMat, TheCenter2);
  VectorKey1:=FuncMethod6_SVR(GramMat, InvariantBase, AffBas, EXT1, "isomorphy", NeedAffBas);
  VectorKey2:=FuncMethod6_SVR(GramMat, InvariantBase, AffBas, EXT2, "isomorphy", NeedAffBas);
  U:=FuncLatticeIsomorphism(CharPair1, VectorKey1.SVR, VectorKey1.AffBas, CharPair2, VectorKey2.SVR, VectorKey2.AffBas);
  if U=false then
    return false;
  fi;
  if U[1][1]=-1 then
    RetMat:=-Inverse(U);
  else
    RetMat:=Inverse(U);
  fi;
  if TheCenter1*RetMat<>TheCenter2 then
    Error("We have an inconsistency here, please panic!!!");
  fi;
  return RetMat;
end;


# the group must be the natural group of the lattice
# TheCenterI has to be the center of the empty sphere around EXTI
Equivalence_Method6:=function(DataLattice, EXT1, EXT2, TheCenter1, TheCenter2)
  return M6_Equivalence(DataLattice.GramMat, DataLattice.InvariantBase, DataLattice.AffBas, DataLattice.FuncLatticeIsomorphism, EXT1, EXT2, TheCenter1, TheCenter2, DataLattice.NeedAffBas);
end;



TestEquivalenceOfDelaunay:=function(DataLattice, EXT1, EXT2, Delaunay1Stab)
  local CP1, CP2, TheCenter1, TheCenter2, DM1, DM2, test, ePerm, GRP1, REP, LFactors1, TheQuot, LimitEfficiencyNauty;
  CP1:=CenterRadiusDelaunayPolytopeGeneral(DataLattice.GramMat, EXT1);
  TheCenter1:=CP1.Center;
  CP2:=CenterRadiusDelaunayPolytopeGeneral(DataLattice.GramMat, EXT2);
  TheCenter2:=CP2.Center;
  LimitEfficiencyNauty:=2000;
  if Length(EXT1)<LimitEfficiencyNauty then
    DM1:=DistanceMatrixDelaunay(DataLattice.GramMat, EXT1);
    DM2:=DistanceMatrixDelaunay(DataLattice.GramMat, EXT2);
    test:=IsIsomorphicEdgeColoredGraph(DM1, DM2);
    if test=false then
      return false;
    fi;
    ePerm:=PermList(test);
    GRP1:=Delaunay1Stab.PrivateInfo.GRP;
  fi;
  Print("|V|=", Length(EXT1));
  Print("  |LattIsom|=", Order(Delaunay1Stab.PermutationStabilizer));
  if Length(EXT1) < LimitEfficiencyNauty then
    Print("  |Isom|=", Order(GRP1));
  fi;
  if IsVectorRational(TheCenter1)=true then
    LFactors1:=FactorsInt(ListFactors(TheCenter1));
  else
    LFactors1:="undefined";
  fi;
  #
#  Print("  ListFactors=", LFactors1);
  Print("\n");
  if Length(EXT1)<LimitEfficiencyNauty then
    REP:=Equivalence_Method0(DataLattice, EXT1, EXT2, Delaunay1Stab, ePerm);
    TheQuot:=Order(GRP1)/Order(Delaunay1Stab.PermutationStabilizer);
  else
    REP:=fail;
    TheQuot:=10000000000000000000000000000000;
  fi;
  if REP<>fail then
    return REP;
  else
    if DataLattice.n<=7 then
      return Equivalence_Method2(DataLattice, TheCenter1, TheCenter2);
    fi;
    if Length(EXT1)<LimitEfficiencyNauty then
      if Order(GRP1)<=50000 then
        return Equivalence_Method4(DataLattice, EXT1, EXT2, GRP1, ePerm);
      fi;
    fi;
    if LFactors1<>"undefined" and Length(LFactors1)>2 then
      return Equivalence_Method3(DataLattice, TheCenter1, TheCenter2);
    fi;
    if TheQuot< 100 then
      return Equivalence_Method5(DataLattice, EXT1, EXT2, Delaunay1Stab, ePerm);
    fi;
    return Equivalence_Method6(DataLattice, EXT1, EXT2, TheCenter1, TheCenter2);
  fi;
end;


InvariantMatching:=function()
  local TheSetInvariant, TheListPosition, nbElt, GetListMatching, FuncInsert;
  TheSetInvariant:=[];
  TheListPosition:=[];
  nbElt:=0;
  GetListMatching:=function(eInv)
    local pos;
    pos:=Position(TheSetInvariant, eInv);
    if pos=fail then
      return [];
    else
      return TheListPosition[pos];
    fi;
  end;
  FuncInsert:=function(eInv)
    local NewPos, pos, ePerm;
    nbElt:=nbElt+1;
    NewPos:=nbElt;
    pos:=Position(TheSetInvariant, eInv);
    if pos<>fail then
      Add(TheListPosition[pos], NewPos);
    else
      Add(TheSetInvariant, eInv);
      Add(TheListPosition, [NewPos]);
      ePerm:=SortingPerm(TheSetInvariant);
      TheSetInvariant:=Set(TheSetInvariant);
      TheListPosition:=Permuted(TheListPosition, ePerm);
    fi;
  end;
  return rec(FuncInsert:=FuncInsert,
             GetListMatching:=GetListMatching);
end;





DelaunayDatabaseManagement:=function(PathDelaunay, IsSaving, MemorySave)
  local ListDelaunayEXT, ListDelaunayINV, ListDelaunayGroup, ListDelaunayAdjacencies, ListDelaunayStatus, FuncInsertAdjacencies, FuncDelaunayGetNumber, FuncDelaunayGetEXT, FuncDelaunayGetINV, FuncDelaunayGetGroup, FuncDelaunayGetAdjacencies, FuncDelaunayGetStatus, FuncReturnCompleteDescription, FuncInsertDelaunay, Recover, FuncDestroyDatabase, FuncDelaunayGetNbEXT, ListDelaunayNbEXT, PathDelaunayEXT, PathDelaunayADJ, PathDelaunayINV, PathDelaunayGRP, FuncReturnSingleDelaunayComplete, FuncWriteAsSingleFile, IsInitialized, GetInitState, PathDelaunayPOLY;
  if MemorySave=true and IsSaving=false then
    Error("You cannot save memory without using disk, sorry for that");
  fi;
  IsInitialized:=false;
  PathDelaunayEXT:=Concatenation(PathDelaunay, "ListEXT/");
  PathDelaunayPOLY:=Concatenation(PathDelaunay, "ListPOLY/");
  PathDelaunayADJ:=Concatenation(PathDelaunay, "ListADJ/");
  PathDelaunayINV:=Concatenation(PathDelaunay, "ListINV/");
  PathDelaunayGRP:=Concatenation(PathDelaunay, "ListGRP/");
  if IsSaving=true then
    Exec("mkdir -p ", PathDelaunayEXT);
    Exec("mkdir -p ", PathDelaunayPOLY);
    Exec("mkdir -p ", PathDelaunayADJ);
    Exec("mkdir -p ", PathDelaunayINV);
    Exec("mkdir -p ", PathDelaunayGRP);
  fi;
  ListDelaunayEXT:=[];
  ListDelaunayINV:=[];
  ListDelaunayNbEXT:=[];
  ListDelaunayGroup:=[];
  ListDelaunayAdjacencies:=[];
  ListDelaunayStatus:=[];
  FuncInsertDelaunay:=function(TheEXT, TheINV, TheStab)
    local nbDelaunay, FileDelaunayEXT, FileDelaunayINV, FileGroup;
    IsInitialized:=true;
    Add(ListDelaunayINV, TheINV);
    Add(ListDelaunayStatus, "NO");
    Add(ListDelaunayNbEXT, Length(TheEXT));
    if MemorySave=false then
      Add(ListDelaunayEXT, TheEXT);
      Add(ListDelaunayGroup, TheStab);
    fi;
    nbDelaunay:=Length(ListDelaunayStatus);
    FileDelaunayEXT:=Concatenation(PathDelaunayEXT, "DelaunayEXT", String(nbDelaunay));
    SaveDataToFilePlusTouchPlusTest(FileDelaunayEXT, TheEXT, IsSaving);
    FileDelaunayINV:=Concatenation(PathDelaunayINV, "DelaunayINV", String(nbDelaunay));
    SaveDataToFilePlusTouchPlusTest(FileDelaunayINV, TheINV, IsSaving);
    FileGroup:=Concatenation(PathDelaunayGRP, "DelaunayGroup", String(nbDelaunay));
    SaveDataToFilePlusTouchPlusTest(FileGroup, TheStab, IsSaving);
  end;
  FuncInsertAdjacencies:=function(iDel, Adjacencies)
    local FileDelaunayAdd;
    IsInitialized:=true;
    if MemorySave=false then
      ListDelaunayAdjacencies[iDel]:=Adjacencies;
    fi;
    FileDelaunayAdd:=Concatenation(PathDelaunayADJ, "DelaunayAdjacencies", String(iDel));
    SaveDataToFilePlusTouchPlusTest(FileDelaunayAdd, Adjacencies, IsSaving);
    ListDelaunayStatus[iDel]:="YES";
  end;
  FuncDestroyDatabase:=function()
    local iOrb, FileDelaunayEXT, FileDelaunayINV, FileDelaunayGroup, FileDelaunayAdjacencies;
    for iOrb in [1..Length(ListDelaunayStatus)]
    do
      FileDelaunayEXT:=Concatenation(PathDelaunayEXT, "DelaunayEXT", String(iOrb));
      FileDelaunayINV:=Concatenation(PathDelaunayINV, "DelaunayINV", String(iOrb));
      FileDelaunayGroup:=Concatenation(PathDelaunayGRP, "DelaunayGroup", String(iOrb));
      FileDelaunayAdjacencies:=Concatenation(PathDelaunayADJ, "DelaunayAdjacencies", String(iOrb));
      RemoveFileIfExistPlusTouchPlusTest(FileDelaunayEXT, IsSaving);
      RemoveFileIfExistPlusTouchPlusTest(FileDelaunayINV, IsSaving);
      RemoveFileIfExistPlusTouchPlusTest(FileDelaunayGroup, IsSaving);
      RemoveFileIfExistPlusTouchPlusTest(FileDelaunayAdjacencies, IsSaving);
    od;
    if IsSaving=true then
#     NEED TO BE CAREFUL ABOUT THIS
#      Exec("rm -r ", PathDelaunay, "ListEXT");
#      Exec("rm -r ", PathDelaunay, "ListADJ");
#      Exec("rm -r ", PathDelaunay, "ListINV");
#      Exec("rm -r ", PathDelaunay, "ListGRP");
    fi;
  end;
  Recover:=function()
    local iOrb, FileDelaunayEXT, FileDelaunayINV, FileDelaunayGroup, FileDelaunayAdjacencies, Adjacencies, TheEXT, TheGroup, TheINV;
    if IsInitialized=true then
      return;
    fi;
    iOrb:=1;
    while(true)
    do
      FileDelaunayEXT:=Concatenation(PathDelaunayEXT, "DelaunayEXT", String(iOrb));
      FileDelaunayINV:=Concatenation(PathDelaunayINV, "DelaunayINV", String(iOrb));
      FileDelaunayGroup:=Concatenation(PathDelaunayGRP, "DelaunayGroup", String(iOrb));
      FileDelaunayAdjacencies:=Concatenation(PathDelaunayADJ, "DelaunayAdjacencies", String(iOrb));
      if IsExistingFilePlusTouchPlusTest(FileDelaunayEXT, IsSaving)=true and IsExistingFilePlusTouchPlusTest(FileDelaunayINV, IsSaving)=true and IsExistingFilePlusTouchPlusTest(FileDelaunayGroup, IsSaving)=true then
        TheEXT:=ReadAsFunction(FileDelaunayEXT)();
        Add(ListDelaunayNbEXT, Length(TheEXT));
        if MemorySave=false then
          TheGroup:=ReadAsFunction(FileDelaunayGroup)();
          Add(ListDelaunayEXT, TheEXT);
          Add(ListDelaunayGroup, TheGroup);
        fi;
        TheINV:=ReadAsFunction(FileDelaunayINV)();
        Add(ListDelaunayINV, TheINV);
        Add(ListDelaunayStatus, "NO");
        if IsExistingFilePlusTouch(FileDelaunayAdjacencies)=true then
          if MemorySave=false then
            Adjacencies:=ReadAsFunction(FileDelaunayAdjacencies)();
            ListDelaunayAdjacencies[iOrb]:=Adjacencies;
          fi;
          ListDelaunayStatus[iOrb]:="YES";
        fi;
      else
        break;
      fi;
      iOrb:=iOrb+1;
    od;
    IsInitialized:=true;
  end;
  FuncDelaunayGetNumber:=function()
    return Length(ListDelaunayINV);
  end;
  FuncDelaunayGetNbEXT:=function(iOrb)
    return ListDelaunayNbEXT[iOrb];
  end;
  FuncDelaunayGetEXT:=function(iOrb)
    local FileDelaunayEXT;
    if MemorySave=true then
      FileDelaunayEXT:=Concatenation(PathDelaunayEXT, "DelaunayEXT", String(iOrb));
      return ReadAsFunction(FileDelaunayEXT)();
    fi;
    return ListDelaunayEXT[iOrb];
  end;
  FuncDelaunayGetINV:=function(iOrb)
    return ListDelaunayINV[iOrb];
  end;
  FuncDelaunayGetGroup:=function(iOrb)
    local FileDelaunayGroup;
    if MemorySave=true then
      FileDelaunayGroup:=Concatenation(PathDelaunayGRP, "DelaunayGroup", String(iOrb));
      return ReadAsFunction(FileDelaunayGroup)();
    fi;
    return ListDelaunayGroup[iOrb];
  end;
  FuncDelaunayGetStatus:=function(iOrb)
    return ListDelaunayStatus[iOrb];
  end;
  FuncDelaunayGetAdjacencies:=function(iOrb)
    local FileDelaunayAdjacencies;
    if MemorySave=true then
      FileDelaunayAdjacencies:=Concatenation(PathDelaunayADJ, "DelaunayAdjacencies", String(iOrb));
      return ReadAsFunction(FileDelaunayAdjacencies)();
    fi;
    return ListDelaunayAdjacencies[iOrb];
  end;
  FuncReturnSingleDelaunayComplete:=function(iOrb)
    return rec(EXT:=FuncDelaunayGetEXT(iOrb),
               Linv:=FuncDelaunayGetINV(iOrb),
               TheStab:=FuncDelaunayGetGroup(iOrb),
               Adjacencies:=FuncDelaunayGetAdjacencies(iOrb));
  end;
  FuncReturnCompleteDescription:=function()
    local ListOrbitDelaunay, iOrb;
    ListOrbitDelaunay:=[];
    for iOrb in [1..FuncDelaunayGetNumber()]
    do
      Add(ListOrbitDelaunay, FuncReturnSingleDelaunayComplete(iOrb));
    od;
    return ListOrbitDelaunay;
  end;
  GetInitState:=function()
    return IsInitialized;
  end;
  return rec(GetInitState:=GetInitState,
             FuncInsertDelaunay:=FuncInsertDelaunay,
             FuncInsertAdjacencies:=FuncInsertAdjacencies,
             FuncDelaunayGetNbEXT:=FuncDelaunayGetNbEXT,
             Recover:=Recover,
             FuncDelaunayGetNumber:=FuncDelaunayGetNumber,
             FuncDelaunayGetEXT:=FuncDelaunayGetEXT,
             FuncDelaunayGetINV:=FuncDelaunayGetINV,
             FuncDelaunayGetGroup:=FuncDelaunayGetGroup,
             FuncDestroyDatabase:=FuncDestroyDatabase,
             FuncDelaunayGetAdjacencies:=FuncDelaunayGetAdjacencies,
             FuncDelaunayGetStatus:=FuncDelaunayGetStatus,
             FuncReturnSingleDelaunayComplete:=FuncReturnSingleDelaunayComplete,
             FuncReturnCompleteDescription:=FuncReturnCompleteDescription);
end;







ComputeDelaunayDecomposition:=function(DataLattice, DataPolyhedral, DelaunayDatabase)
  local n, EXT, FuncInsert, iOrb, IsFinished, EST, Adjacencies, EXTnew, TheStab, BF, FilePolyhedralOrb, ListOrbit, eOrb, iOrbAdj, iOrbSelect, ThePath, FileSingleAdjacency, BankPath, FuncClearComputation, MinSize, nbV, IsFirst, TheAdj, TheTestAdj;
  ThePath:=DataLattice.PathPermanent;
  BankPath:=Concatenation(ThePath, "TheBank/");
  if DataLattice.Saving=true then
    Exec("mkdir -p ", BankPath);
  fi;
  n:=DataLattice.n;
  FuncClearComputation:=function()
    BF.FuncClearAccount();
    DelaunayDatabase.FuncDestroyDatabase();
  end;
  BF:=BankRecording(rec(Saving:=DataLattice.Saving, BankPath:=BankPath), DataPolyhedral.FuncStabilizer, DataPolyhedral.FuncIsomorphy, DataPolyhedral.FuncInvariant, DataPolyhedral.GroupFormalism);
  FuncInsert:=function(EXT)
    local MyInv, iDelaunay, reply, TheStab, TheEXT, TheTest;
    MyInv:=DataLattice.FuncInvariant(DataLattice, EXT);
    Print("|Database|=", DelaunayDatabase.FuncDelaunayGetNumber(), "\n");
    for iDelaunay in [1..DelaunayDatabase.FuncDelaunayGetNumber()]
    do
      if MyInv=DelaunayDatabase.FuncDelaunayGetINV(iDelaunay) then
        TheEXT:=DelaunayDatabase.FuncDelaunayGetEXT(iDelaunay);
        TheStab:=DelaunayDatabase.FuncDelaunayGetGroup(iDelaunay);
        reply:=DataLattice.FuncIsomorphismDelaunay(DataLattice, TheEXT, EXT, TheStab);
        if reply<>false then
          return rec(success:=1, result:=rec(eBigMat:=reply, iDelaunay:=iDelaunay));
        fi;
      fi;
    od;
    Print("Find polyhedral object with |EXT|=", Length(EXT), "\n");
    TheTest:=DataLattice.KillingDelaunay(EXT);
    if TheTest<>false then
      return rec(success:=0, Reason:=TheTest);
    fi;
    TheStab:=DataLattice.FuncStabilizerDelaunay(DataLattice, EXT);
    DelaunayDatabase.FuncInsertDelaunay(EXT, MyInv, TheStab);
    Print("Find Delaunay: ");
    Print(" |V|=", Length(EXT), " ");
    Print(" |LattIsom|=", Order(TheStab.PermutationStabilizer));
    Print("\n");
    return rec(success:=1, result:=rec(eBigMat:=IdentityMat(n+1), iDelaunay:=DelaunayDatabase.FuncDelaunayGetNumber()));
  end;
  DelaunayDatabase.Recover();
  if DelaunayDatabase.FuncDelaunayGetNumber()=0 then
    EXT:=DataLattice.FindDelaunayPolytope();
    EST:=FuncInsert(EXT);
    if EST.success=0 then
      FuncClearComputation();
      return EST.Reason;
    fi;
  fi;
  while(true)
  do
    IsFinished:=true;
    IsFirst:=true;
    MinSize:=0;
    iOrbSelect:=-1;
    for iOrb in [1..DelaunayDatabase.FuncDelaunayGetNumber()]
    do
      if DelaunayDatabase.FuncDelaunayGetStatus(iOrb)="NO" then
        nbV:=DelaunayDatabase.FuncDelaunayGetNbEXT(iOrb);
        if nbV < MinSize or IsFirst=true then
          MinSize:=nbV;
          iOrbSelect:=iOrb;
          IsFinished:=false;
        fi;
        IsFirst:=false;
      fi;
    od;
    if IsFinished=false then
      TheStab:=DelaunayDatabase.FuncDelaunayGetGroup(iOrbSelect);
      EXT:=DelaunayDatabase.FuncDelaunayGetEXT(iOrbSelect);
      Print("Starting the analysis of Delaunay ", iOrbSelect, " with ", Length(EXT), " vertices\n");
      Print("Beginning the polyhedral computation\n");
      FilePolyhedralOrb:=Concatenation(ThePath, "ListPOLY/PolyhedralSave", String(iOrbSelect));
      ListOrbit:=ComputeAndSavePlusTouchPlusTest(FilePolyhedralOrb, x->__ListFacetByAdjacencyDecompositionMethod(EXT, TheStab.PermutationStabilizer, DataPolyhedral, BF), DataLattice.Saving);
      Print("   Ending the polyhedral computation, |ListOrbit|=", Length(ListOrbit), "\n");
      #
      #
      Adjacencies:=[];
      for iOrbAdj in [1..Length(ListOrbit)]
      do
        FileSingleAdjacency:=Concatenation(ThePath, "SingleAdj_", String(iOrbSelect), "_", String(iOrbAdj));
        if IsExistingFilePlusTouchPlusTest(FileSingleAdjacency, DataLattice.Saving)=true then
          TheAdj:=ReadAsFunction(FileSingleAdjacency)();
        else
          Print("iOrbAdj=", iOrbAdj, "/", Length(ListOrbit), "\n");
          eOrb:=ListOrbit[iOrbAdj];
          EXTnew:=DataLattice.FindAdjacentDelaunay(EXT, eOrb);
          TheTestAdj:=DataLattice.KillingAdjacency(EXT, EXTnew);
          if TheTestAdj<>false then
            FuncClearComputation();
            return TheTestAdj;
          fi;
          EST:=FuncInsert(EXTnew);
          if EST.success=0 then
            FuncClearComputation();
            return EST.Reason;
          fi;
          TheAdj:=EST.result;
          TheAdj.eInc:=eOrb;
          SaveDataToFilePlusTouchPlusTest(FileSingleAdjacency, TheAdj, DataLattice.Saving);
        fi;
        Add(Adjacencies, TheAdj);
      od;
      Print("Adjacency work finished for Orbit ", iOrbSelect, "/", DelaunayDatabase.FuncDelaunayGetNumber(), " orbits\n");
      #
      #
      for iOrbAdj in [1..Length(Adjacencies)]
      do
        FileSingleAdjacency:=Concatenation(ThePath, "SingleAdj_", String(iOrbSelect), "_", String(iOrbAdj));
        RemoveFileIfExistPlusTouchPlusTest(FileSingleAdjacency, DataLattice.Saving);
      od;
      DelaunayDatabase.FuncInsertAdjacencies(iOrbSelect, Adjacencies);
    else
      break;
    fi;
  od;
  Print("Delaunay computation finished\n");
  return "all was ok";
end;


GetMaxNbCharMatrix:=function(eMat)
  local MaxNbChar, eLine, eCol, eStr;
  MaxNbChar:=0;
  for eLine in eMat
  do
    for eCol in eLine
    do
      eStr:=String(eCol);
      MaxNbChar:=Maximum(MaxNbChar, Length(eStr));
    od;
  od;
  return MaxNbChar;
end;


PrintRationalMatrix:=function(output, eMat)
  local ListString, nbLine, nbCol, MaxNbChar, iLine, eLine, eCol, eStr, nb, i;
  MaxNbChar:=GetMaxNbCharMatrix(eMat);
  for eLine in eMat
  do
    for eCol in eLine
    do
      eStr:=String(eCol);
      nb:=1+MaxNbChar - Length(eStr);
      for i in [1..nb]
      do
        AppendTo(output, " ");
      od;
      AppendTo(output, eStr);
    od;
    AppendTo(output, "\n");
  od;
end;


RadiusesAndDelaunayCenterDistances:=function(output, DelaunayDatabase, DataLattice)
  local n, iDelaunay, TheEXT, CP, EFRL, iOrb, eAdj, Center1, Center2, H1, H2, dist, nbDel, ListRadius, ListCenters, EXT, TheOrder, TheStab, SHV, EXTred, i;
  n:=DataLattice.n;
  DelaunayDatabase.Recover();
  nbDel:=DelaunayDatabase.FuncDelaunayGetNumber();
  Print("nbDel=", nbDel, "\n");
  AppendTo(output, "n=", n, "\n");
  AppendTo(output, "Gram matrix is\n");
  PrintRationalMatrix(output, DataLattice.GramMat);
  AppendTo(output, "Determinant GramMat=", DeterminantMat(DataLattice.GramMat), "\n");
#  AppendTo(output, "|Aut(Lattice)|=", Size(DataLattice.PointGRP), "\n");
  SHV:=ShortestVectorDutourVersion(DataLattice.GramMat);
  if Length(SHV)<100 then
    AppendTo(output, "List of shortest vectors is\n");
    PrintRationalMatrix(output, SHV);
  fi;
  AppendTo(output, "We have ", nbDel, " orbits of Delaunay polytopes\n");
  ListRadius:=[];
  ListCenters:=[];
  for iDelaunay in [1..nbDel]
  do
    EXT:=DelaunayDatabase.FuncDelaunayGetEXT(iDelaunay);
    CP:=CenterRadiusDelaunayPolytopeGeneral(DataLattice.GramMat, EXT);
    Add(ListCenters, CP.Center);
    Add(ListRadius, CP.SquareRadius);
  od;
  Print("Delaunay centers have been determined\n");
  for iDelaunay in [1..nbDel]
  do
    TheEXT:=DelaunayDatabase.FuncDelaunayGetEXT(iDelaunay);
    TheStab:=DelaunayDatabase.FuncDelaunayGetGroup(iDelaunay);
    AppendTo(output, "Orbit ", iDelaunay, " : ");
    AppendTo(output, "  nbV=", Length(TheEXT));
    if IsGroup(TheStab.PermutationStabilizer)=true then
      TheOrder:=Order(TheStab.PermutationStabilizer);
    else
      TheOrder:=TheStab.Order;
    fi;
    AppendTo(output, "  OrdStab=", TheOrder);
    AppendTo(output, "  SqrRadius=", ListRadius[iDelaunay]);
    AppendTo(output, "\n");
    Center1:=ListCenters[iDelaunay];
    AppendTo(output, "Center=");
    for i in [1..n]
    do
      AppendTo(output, Center1[i], " ");
    od;
    AppendTo(output, "\n");
    AppendTo(output, "List of vertices is:\n");
    EXT:=DelaunayDatabase.FuncDelaunayGetEXT(iDelaunay);
    EXTred:=List(EXT, x->x{[2..n+1]});
    PrintRationalMatrix(output, EXTred);
    EFRL:=DelaunayDatabase.FuncDelaunayGetAdjacencies(iDelaunay);
    AppendTo(output, "We have ", Length(EFRL), " orbits of facets\n");
    for iOrb in [1..Length(EFRL)]
    do
      eAdj:=EFRL[iOrb];
      Center2:=ListCenters[eAdj.iDelaunay]*eAdj.eBigMat;
      H1:=Center2-Center1;
      H2:=H1{[2..n+1]};
      dist:=H2*DataLattice.GramMat*H2;
      AppendTo(output, "  Orbit ", iOrb);
      AppendTo(output, " AdjOrbit=", eAdj.iDelaunay);
      AppendTo(output, " SqrDist=", dist);
      AppendTo(output, "\n");
    od;
    AppendTo(output, "\n");
  od;
  AppendTo(output, "Max Square Radius=", Maximum(ListRadius), "\n");
end;


#
#
# For isomorphy tests in the ADM, we can choose a different
# group formalism. This can help speed up performance.
# see below the standard PermutationGroup + OnSets formalism
OnSetsGroupFormalismDelaunay:=function(DataLattice)
  local __LiftingOrbits, OnSetsRepresentativeAction, OnSetsStabilizer, GroupUnion, ToPermGroup, TheOrder, OnSetsIsSubgroup, OnSetsGroupConjugacy, OnSetsTransformIncidenceList, MyOrbitGroupFormalism, BankKeyInformation, BankCompleteInformation, BankGetVertexSet, BankGetGroup, BankGetListObject, BankGetForIsom;
  __LiftingOrbits:=function(EXT, ListInc, SmallGroup, BigGroup)
    local NewListInc, eInc;
    NewListInc:=[];
    for eInc in ListInc
    do
      Append(NewListInc, __IndividualLifting(eInc, SmallGroup, BigGroup));
    od;
    return NewListInc;
  end;
  OnSetsStabilizer:=function(EXT, GRP, eInc)
    return SecondReduceGroupAction(Stabilizer(GRP, eInc, OnSets), eInc);
  end;
  GroupUnion:=function(Grp1, Grp2)
    return PersoGroupPerm(SmallGeneratingSet(Group(Union(GeneratorsOfGroup(Grp1), GeneratorsOfGroup(Grp2)))));
  end;
  ToPermGroup:=function(EXT, Grp)
    return Grp;
  end;
  TheOrder:=function(GRP)
    return Order(GRP);
  end;
  OnSetsIsSubgroup:=function(GRP1, GRP2)
    return IsSubgroup(GRP1, GRP2);
  end;
  OnSetsGroupConjugacy:=function(GRP, eElt)
    local NewGens, eGen;
    NewGens:=[];
    for eGen in GeneratorsOfGroup(GRP)
    do
      Add(NewGens, eElt^(-1)*eGen*eElt);
    od;
    return PersoGroupPerm(NewGens);
  end;
  OnSetsTransformIncidenceList:=function(ListEXT1, ListEXT2, TheEquiv, ListListInc)
    return List(ListListInc, x->OnSets(x, TheEquiv));
  end;
  MyOrbitGroupFormalism:=function(EXT, TheGroup, Prefix, SavingTrigger)
    local FuncInvariant, FuncIsomorphy, FuncInvariantUpdate, OrderLincStabilizer, GetOrbitIntersection, FuncGetInitialDisc;
    FuncGetInitialDisc:=function()
      return [];
    end;
    FuncInvariant:=function(Odisc, Linc)
      return DelaunayInvariantLattice(DataLattice, EXT{Linc});
    end;
    FuncIsomorphy:=function(Linc1, Linc2)
      return RepresentativeAction(TheGroup, Linc1, Linc2, OnSets)<>fail;
    end;
    FuncInvariantUpdate:=function(OdiscPrev, NbCall)
      return [];
    end;
    OrderLincStabilizer:=function(Linc)
      return Order(Stabilizer(TheGroup, Linc, OnSets));
    end;
    GetOrbitIntersection:=function(eSet)
      return OrbitIntersection(eSet, TheGroup);
    end;
    return OrbitGroupFormalism(EXT, TheGroup, Prefix, SavingTrigger,
        rec(FuncGetInitialDisc:=FuncGetInitialDisc,
            FuncInvariant:=FuncInvariant,
            FuncIsomorphy:=FuncIsomorphy,
            GetOrbitIntersection:=GetOrbitIntersection,
            GroupOrder:=Order(TheGroup),
            OrderLincStabilizer:=OrderLincStabilizer,
            FuncInvariantUpdate:=FuncInvariantUpdate));
  end;
  BankKeyInformation:=function(EXT, GroupExt)
    return rec(EXT:=EXT, Group:=GroupExt);
  end;
  BankCompleteInformation:=function(EXT, GroupExt, ListObject)
    return ListObject;
  end;
  BankGetVertexSet:=function(TheKey, TheComplete)
    return TheKey.EXT;
  end;
  BankGetGroup:=function(TheKey, TheComplete)
    return TheKey.Group;
  end;
  BankGetListObject:=function(TheComplete)
    return TheComplete;
  end;
  BankGetForIsom:=function(TheKey)
    return TheKey.EXT;
  end;
  return rec(
    Stabilizer:=OnSetsStabilizer,
    LiftingOrbits:=__LiftingOrbits,
    GroupUnion:=GroupUnion,
    ToPermGroup:=ToPermGroup,
    Order:=TheOrder,
    IsSubgroup:=OnSetsIsSubgroup,
    GroupConjugacy:=OnSetsGroupConjugacy,
    TransformIncidenceList:=OnSetsTransformIncidenceList,
    OrbitGroupFormalism:=MyOrbitGroupFormalism,
    BankKeyInformation:=BankKeyInformation,
    BankCompleteInformation:=BankCompleteInformation,
    BankGetForIsom:=BankGetForIsom,
    BankGetVertexSet:=BankGetVertexSet,
    BankGetGroup:=BankGetGroup,
    BankGetListObject:=BankGetListObject);
end;








ForKernel_DataLatticePolyhedralDatabase:=function(TheGramMat, PointGRP, ThePrefix, IsSaving, MaximalMemorySave, RecSVR)
  local n, MatrixGRP, eGen, FuncEquiv, FuncAutom, IsRespawn, IsBankSave, PathTMP, PathSAVE, DataPolyhedral, DataLattice, PathPermanent, SVR, TheInvariantBase, FuncStabilizer, FuncIsomorphy, DelaunayDatabase, TestBelonging, ListPermGens, MatrGens, PermGRP, phi, FindDelaunay, FindAdjacentDelaunay, TheReply, FuncInvariant, WorkingAffineBasis, MyOption, FuncLatticeAutomorphism, FuncLatticeIsomorphism, FindClosestElement, KillingDelaunay, KillingAdjacency;
  n:=Length(TheGramMat);
  MatrixGRP:=Group(List(GeneratorsOfGroup(PointGRP), x->FuncCreateBigMatrix(ListWithIdenticalEntries(n,0), x)));
  FindAdjacentDelaunay:=function(EXT, eOrb)
    local EXTadj;
#    Print("Before call to FindAdjacentDelaunayPolytope\n");
    EXTadj:=FindAdjacentDelaunayPolytope(TheGramMat, EXT, eOrb);
#    Print("After call to FindAdjacentDelaunayPolytope\n");
    return EXTadj;
  end;
  FindClosestElement:=function(eVect)
    return CVPVallentinProgram(TheGramMat, eVect);
  end;
  if ThePrefix[Length(ThePrefix)]<>'/' then
    Error("Last character of ThePrefix=", ThePrefix, " should be /");
  fi;
  FuncEquiv:=function(EXT1, EXT2, ThePoint1, ThePoint2)
    return Equivalence_Method6(DataLattice, EXT1, EXT2, ThePoint1, ThePoint2);
  end;
  FuncAutom:=function(EXT, ThePoint)
    local GRP1, RedPoint, MatrixGens, eMat, eTrans, GRPret;
    GRP1:=Stabilizer_Method6(DataLattice, EXT, ThePoint);
    RedPoint:=ThePoint{[2..n+1]};
    MatrixGens:=[];
    for eMat in GeneratorsOfGroup(GRP1)
    do
      eTrans:=RedPoint-RedPoint*eMat;
      Add(MatrixGens, FuncCreateBigMatrix(eTrans, eMat));
    od;
    GRPret:=Group(MatrixGens);
    SetSize(GRPret, Size(GRP1));
    return GRPret;
  end;
  #
  # checks
  for eGen in GeneratorsOfGroup(PointGRP)
  do
    if TheGramMat<>eGen*TheGramMat*TransposedMat(eGen) then
      Error("Some given symmetries do not prerse the Gram matrix, ERROR!!!");
    fi;
  od;
  #
  #
  # We assumed the group to be the total group
  # If not then do double cosets operations
  TestBelonging:=function(eBigMat)
    return IsIntegralMat(eBigMat);
  end;
  #
  #
  FuncStabilizer:=function(EXT)
    local DM;
    if Length(EXT) < 30 then
      return Group(());
    fi;
    DM:=DistanceMatrixDelaunay(TheGramMat, EXT);
    return AutomorphismGroupEdgeColoredGraph(DM);
  end;
  FuncIsomorphy:=function(EXT1, EXT2)
    local DM1, DM2, test;
    if Length(EXT1)<>Length(EXT2) then
      return false;
    fi;
    DM1:=DistanceMatrixDelaunay(TheGramMat, EXT1);
    DM2:=DistanceMatrixDelaunay(TheGramMat, EXT2);
    test:=IsIsomorphicEdgeColoredGraph(DM1, DM2);
    if test=false then
      return false;
    else
      return PermList(test);
    fi;
  end;
  FuncInvariant:=function(EXT)
    return DelaunayInvariantLattice(rec(GramMat:=TheGramMat), EXT);
  end;
  #
  #
  IsRespawn:=function(OrdGRP, EXT, TheDepth)
    if Length(EXT)>=90 then
      return true;
    fi;
    if TheDepth>=2 then
      return false;
    fi;
    if OrdGRP<=6000 then
      return false;
    fi;
    if Length(EXT)<=36 then
      return false;
    fi;
    return true;
  end;
  IsBankSave:=function(EllapsedTime, OrdGRP, EXT, TheDepth)
    if TheDepth=0 then
      return false;
    fi;
    if EllapsedTime>=600 then
      return true;
    fi;
    if Length(EXT)<=30 then
      return false;
    fi;
    return true;
  end;
  FindDelaunay:=function()
    return FindDelaunayPolytope(TheGramMat);
  end;
  PathTMP:=Concatenation(ThePrefix, "tmp/");
  Exec("mkdir -p ", PathTMP);
  if IsSaving=true then
    PathSAVE:=Concatenation(ThePrefix, "PolyhedralSave/");
    PathPermanent:=Concatenation(ThePrefix, "Saving/");
    Exec("mkdir -p ", PathSAVE);
    Exec("mkdir -p ", PathPermanent);
  else
    PathSAVE:="/irrelevant/";
    PathPermanent:="/irrelevant/";
  fi;
  MyOption:="";
  FuncLatticeAutomorphism:=function(ListMat, SVR, AffBas)
    if AffBas="irrelevant" then
      return ArithmeticAutomorphismMatrixFamily_Nauty(ListMat, SVR);
    else
      return ArithmeticAutomorphismMatrixFamily_HackSouvignier(MyOption, ListMat, SVR, AffBas);
    fi;
  end;
  FuncLatticeIsomorphism:=function(ListMat1, SVR1, AffBas1, ListMat2, SVR2, AffBas2)
    if Length(SVR1)<>Length(SVR2) then
      return false;
    fi;
    if AffBas1="irrelevant" then
      if AffBas2<>"irrelevant" then
        Error("Maybe there is a logical error");
      fi;
      return ArithmeticEquivalenceMatrixFamily_Nauty(ListMat1, SVR1, ListMat2, SVR2);
    else
      return ArithmeticEquivalenceMatrixFamily_HackSouvignier(MyOption, ListMat1, SVR1, AffBas1, ListMat2, SVR2, AffBas2);
    fi;
  end;
  KillingDelaunay:=function(EXT)
    return false;
  end;
  KillingAdjacency:=function(EXT1, EXT2)
    return false;
  end;
  DataPolyhedral:=rec(
    IsBankSave:=IsBankSave,
    IsRespawn:=IsRespawn,
    Saving:=IsSaving,
    ThePath:=PathTMP,
    TheDepth:=0,
    GetInitialRays:=GetInitialRays_LinProg,
    ThePathSave:=PathSAVE,
    DualDescriptionFunction:=poly_private@DualDescriptionLRS_Reduction,
    ProjectionLiftingFramework:=__ProjectionLiftingFramework,
    FuncStabilizer:=FuncStabilizer,
    FuncIsomorphy:=FuncIsomorphy,
    FuncInvariant:=FuncInvariant,
    GroupFormalism:=OnSetsGroupFormalismDelaunay(rec(GramMat:=TheGramMat)));
  if Length(RecSVR.SVRfaithful)>0 then
    ListPermGens:=RetrieveListPermGensFromVectors(RecSVR.SVRfaithful, GeneratorsOfGroup(PointGRP));
  else
    ListPermGens:=[()];
  fi;
  TheInvariantBase:=RecSVR.TheInvariantBase;
  Print("|TheInvariantBase|=", Length(TheInvariantBase), "\n");
  MatrGens:=GeneratorsOfGroup(PointGRP);
  WorkingAffineBasis:=RecSVR.WorkingAffineBasis;
  PermGRP:=Group(ListPermGens);
  phi:=GroupHomomorphismByImages(PermGRP, PointGRP, ListPermGens, MatrGens);
  DataLattice:=rec(
    Saving:=IsSaving,
    PathPermanent:=PathPermanent,
    GramMat:=TheGramMat,
    NeedAffBas:=true,
    n:=n,
    KillingDelaunay:=KillingDelaunay,
    KillingAdjacency:=KillingAdjacency,
    PermGRP:=PermGRP, phi:=phi,
    MatrixGRP:=MatrixGRP,
    PointGRP:=PointGRP,
    FuncEquiv:=FuncEquiv,
    FuncAutom:=FuncAutom,
    FindDelaunayPolytope:=FindDelaunay,
    FuncInvariant:=DelaunayInvariantLattice,
    AffBas:=WorkingAffineBasis,
    TestBelonging:=TestBelonging,
    FuncLatticeAutomorphism:=FuncLatticeAutomorphism,
    FuncLatticeIsomorphism:=FuncLatticeIsomorphism,
    FindAdjacentDelaunay:=FindAdjacentDelaunay,
    FindClosestElement:=FindClosestElement,
    FuncStabilizerDelaunay:=StabilizerOfDelaunay,
    FuncIsomorphismDelaunay:=TestEquivalenceOfDelaunay,
    InvariantBase:=TheInvariantBase);
  DelaunayDatabase:=DelaunayDatabaseManagement(PathPermanent, IsSaving, MaximalMemorySave);
  return rec(DataLattice:=DataLattice, DataPolyhedral:=DataPolyhedral, DelaunayDatabase:=DelaunayDatabase);
end;









DelaunayDescriptionStandardKernel:=function(TheGramMat, PointGRP, ThePrefix, IsSaving, KillingDelaunay, KillingAdjacency, MaximalMemorySave)
  local RecSVR, DLPD, TheReply;
  RecSVR:=GetRecSVR(TheGramMat, PointGRP);
  DLPD:=ForKernel_DataLatticePolyhedralDatabase(TheGramMat, PointGRP, ThePrefix, IsSaving, MaximalMemorySave, RecSVR);
  DLPD.DataLattice.KillingDelaunay:=KillingDelaunay;
  DLPD.DataLattice.KillingAdjacency:=KillingAdjacency;
  TheReply:=ComputeDelaunayDecomposition(DLPD.DataLattice, DLPD.DataPolyhedral, DLPD.DelaunayDatabase);
  if TheReply="all was ok" then
    return DLPD.DelaunayDatabase.FuncReturnCompleteDescription();
  else
    return TheReply;
  fi;
end;







Periodic_StabilizerMethod0:=Stabilizer_Method0;

Periodic_EquivalenceMethod0:=Equivalence_Method0;



Periodic_EquivalenceMethod2:=function(DataLattice, TheCenter1, TheCenter2)
  local n, RedCenterFirst1, RedCenterFirst2, RedCenter1, RedCenter2, FuncRawImage, FuncActionMod1, eElt, eMat, eBigMat, eTrans, PermGRP;
  n:=DataLattice.n;
  RedCenterFirst1:=TheCenter1{[2..n+1]};
  RedCenterFirst2:=TheCenter2{[2..n+1]};
  RedCenter1:=Concatenation([1], VectorMod1(RedCenterFirst1));
  RedCenter2:=Concatenation([1], VectorMod1(RedCenterFirst2));
  PermGRP:=DataLattice.PermGRP;
  FuncRawImage:=function(eElt)
    local nbGen, f, hom, hom2;
    nbGen:=Length(DataLattice.ListMatrGens);
    f:=FreeGroup(nbGen);
    hom:=GroupHomomorphismByImagesNC(f, PermGRP, GeneratorsOfGroup(f), GeneratorsOfGroup(PermGRP));
    hom2:=GroupHomomorphismByImagesNC(f, DataLattice.MatrixGRP, GeneratorsOfGroup(f), GeneratorsOfGroup(DataLattice.MatrixGRP));
    return Image(hom2, PreImagesRepresentative(hom, eElt));
  end;
  FuncActionMod1:=function(eClass, eElt)
    local fClass;
    fClass:=eClass*FuncRawImage(eElt);
    return Concatenation([1], VectorMod1(fClass{[2..n+1]}));
  end;
  eElt:=RepresentativeAction(PermGRP, RedCenter1, RedCenter2, FuncActionMod1);
  if eElt<>fail then
    eBigMat:=FuncRawImage(eElt);
    eMat:=FuncExplodeBigMatrix(eBigMat).MatrixTransformation;
    eTrans:=RedCenterFirst2-RedCenterFirst1*eMat;
    return FuncCreateBigMatrix(eTrans, eMat);
  fi;
  return false;
end;


Periodic_StabilizerMethod2:=function(DataLattice, TheCenter)
  local n, RedCenterFirst, RedCenter, FuncRawImage, FuncActionMod1, PermGRP, PermStab, ListMatStab, GRP;
  n:=DataLattice.n;
  RedCenterFirst:=TheCenter{[2..n+1]};
  RedCenter:=Concatenation([1], VectorMod1(RedCenterFirst));
  PermGRP:=DataLattice.PermGRP;
  FuncRawImage:=function(eElt)
    local nbGen, f, hom, hom2;
    nbGen:=Length(DataLattice.ListMatrGens);
    f:=FreeGroup(nbGen);
    hom:=GroupHomomorphismByImagesNC(f, PermGRP, GeneratorsOfGroup(f), GeneratorsOfGroup(PermGRP));
    hom2:=GroupHomomorphismByImagesNC(f, DataLattice.MatrixGRP, GeneratorsOfGroup(f), GeneratorsOfGroup(DataLattice.MatrixGRP));
    return Image(hom2, PreImagesRepresentative(hom, eElt));
  end;
  FuncActionMod1:=function(eClass, eElt)
    local fClass;
    fClass:=eClass*FuncRawImage(eElt);
    return Concatenation([1], VectorMod1(fClass{[2..n+1]}));
  end;
  PermStab:=Stabilizer(PermGRP, RedCenter, FuncActionMod1);
  ListMatStab:=List(GeneratorsOfGroup(PermStab), x->FuncExplodeBigMatrix(FuncRawImage(x)).MatrixTransformation);
  GRP:=PersoGroupMatrix(ListMatStab, n);
  SetSize(GRP, Order(PermStab));
  return GRP;
end;


GroupDenominators:=function(MatrixGRP)
  local ListVect, eMat;
  ListVect:=[];
  for eMat in GeneratorsOfGroup(MatrixGRP)
  do
    Append(ListVect, FuncExplodeBigMatrix(eMat).eTrans);
  od;
  return ListFactors(ListVect);
end;









Periodic_EquivalenceMethod3:=function(DataLattice, TheCenter1, TheCenter2)
  local n, RedCenterFirst1, RedCenterFirst2, RedCenter1, RedCenter2, RedCenterPrev1, RedCenterPW1, RedCenterPW2, OnClassesModPW, ReductionModPW, FuncRawImage, FuncActionModPW, eElt, eMat, eMatSearch, eTrans, GrpStab, OneDen, GroupDen, LFactors1, LSpaceFactors1, i, PermGRP, ListSequenceDenominator, eDen;
  n:=DataLattice.n;
  RedCenterFirst1:=TheCenter1{[2..n+1]};
  RedCenterFirst2:=TheCenter2{[2..n+1]};
  RedCenter1:=Concatenation([1], VectorMod1(RedCenterFirst1));
  RedCenter2:=Concatenation([1], VectorMod1(RedCenterFirst2));
  GroupDen:=DataLattice.GroupDen;
  LFactors1:=ListFactors(TheCenter1);
  LSpaceFactors1:=FactorsInt(LcmInt(GroupDen, LFactors1)/GroupDen);
  ListSequenceDenominator:=[];
  for i in [1..Length(LSpaceFactors1)-1]
  do
    OneDen:=GroupDen*Product(LSpaceFactors1{[i+1..Length(LSpaceFactors1)]});
    Add(ListSequenceDenominator, OneDen);
  od;
  Add(ListSequenceDenominator, 1);
  PermGRP:=DataLattice.PermGRP;
  #
  FuncRawImage:=function(eElt)
    local nbGen, f, hom, hom2;
    nbGen:=Length(DataLattice.ListMatrGens);
    f:=FreeGroup(nbGen);
    hom:=GroupHomomorphismByImagesNC(f, PermGRP, GeneratorsOfGroup(f), GeneratorsOfGroup(PermGRP));
    hom2:=GroupHomomorphismByImagesNC(f, DataLattice.MatrixGRP, GeneratorsOfGroup(f), GeneratorsOfGroup(DataLattice.MatrixGRP));
    return Image(hom2, PreImagesRepresentative(hom, eElt));
  end;
  #
  RedCenterPrev1:=ShallowCopy(RedCenter1);
  GrpStab:=ShallowCopy(DataLattice.PermGRP);
  eMatSearch:=IdentityMat(n+1);
  for eDen in ListSequenceDenominator
  do
    ReductionModPW:=function(eVect)
      return Concatenation([1], List(eVect{[2..n+1]}, x->FractionModPW(x,eDen)));
    end;
    FuncActionModPW:=function(eClass, eElt)
      return ReductionModPW(eClass*FuncRawImage(eElt));
    end;
    RedCenterPW1:=ReductionModPW(RedCenterPrev1);
    RedCenterPW2:=ReductionModPW(RedCenter2);
    eElt:=RepresentativeAction(GrpStab, RedCenterPW1, RedCenterPW2, FuncActionModPW);
    if eElt=fail then
      return false;
    fi;
    eMat:=FuncRawImage(eElt);
    eMatSearch:=eMatSearch*eMat;
    RedCenterPrev1:=OnClassesMod1(RedCenterPrev1, eMat);
    if RedCenterPrev1=RedCenter2 then
      eMat:=FuncExplodeBigMatrix(eMatSearch).MatrixTransformation;
      eTrans:=RedCenterFirst2-RedCenterFirst1*eMat;
      return FuncCreateBigMatrix(eTrans, eMat);
    fi;
    GrpStab:=Stabilizer(GrpStab, RedCenterPrev1, OnClassesModPW);
    GrpStab:=Group(SmallGeneratingSet(GrpStab));
  od;
end;

Periodic_StabilizerMethod3:=function(DataLattice, TheCenter)
  local n, RedCenterFirst, RedCenter, GroupDen, LFactors, LSpaceFactors, ListSequenceDenominator, i, OneDen, PermStab, TheOrd, FuncRawImage, eDen, ReductionModPW, FuncActionModPW, RedCenterPW, eComp, GRP, ListMatStab;
  n:=DataLattice.n;
  RedCenterFirst:=TheCenter{[2..n+1]};
  RedCenter:=Concatenation([1], VectorMod1(RedCenterFirst));
  GroupDen:=DataLattice.GroupDen;
  LFactors:=ListFactors(TheCenter);
  LSpaceFactors:=FactorsInt(LcmInt(GroupDen, LFactors)/GroupDen);
  ListSequenceDenominator:=[];
  for i in [1..Length(LSpaceFactors)-1]
  do
    OneDen:=GroupDen*Product(LSpaceFactors{[i+1..Length(LSpaceFactors)]});
    Add(ListSequenceDenominator, OneDen);
  od;
  Add(ListSequenceDenominator, 1);
  PermStab:=ShallowCopy(DataLattice.PermGRP);
  TheOrd:=Size(DataLattice.PermGRP);
  FuncRawImage:=function(eElt)
    local nbGen, f, hom, hom2;
    nbGen:=Length(DataLattice.ListMatrGens);
    f:=FreeGroup(nbGen);
    hom:=GroupHomomorphismByImagesNC(f, DataLattice.PermGRP, GeneratorsOfGroup(f), GeneratorsOfGroup(DataLattice.PermGRP));
    hom2:=GroupHomomorphismByImagesNC(f, DataLattice.MatrixGRP, GeneratorsOfGroup(f), GeneratorsOfGroup(DataLattice.MatrixGRP));
    return Image(hom2, PreImagesRepresentative(hom, eElt));
  end;
  #
  for eDen in ListSequenceDenominator
  do
    ReductionModPW:=function(eVect)
      return Concatenation([1], List(eVect{[2..n+1]}, x->FractionModPW(x,eDen)));
    end;
    FuncActionModPW:=function(eClass, eElt)
      return ReductionModPW(eClass*FuncRawImage(eElt));
    end;
    RedCenterPW:=ReductionModPW(RedCenterFirst);
    eComp:=OrbitStabilizer(PermStab, RedCenterPW, FuncActionModPW);
    PermStab:=eComp.stabilizer;
    TheOrd:=TheOrd/Length(eComp.orbit);
    PermStab:=Group(SmallGeneratingSet(PermStab));
  od;
  ListMatStab:=List(GeneratorsOfGroup(PermStab), x->FuncExplodeBigMatrix(FuncRawImage(x)).MatrixTransformation);
  GRP:=Group(ListMatStab);
  SetSize(GRP, TheOrd);
  return GRP;
end;




Periodic_EquivalenceMethod4:=Equivalence_Method4;

Periodic_StabilizerMethod4:=Stabilizer_Method4;

Periodic_EquivalenceMethod6:=function(DataLattice, EXT1, EXT2, ThePoint1, ThePoint2)
  local eBigMat, imgThePoint2, imgEXT2, TheEquiv;
  for eBigMat in DataLattice.TheComp.ListElement
  do
    imgThePoint2:=ThePoint2*eBigMat;
    imgEXT2:=EXT2*eBigMat;
    TheEquiv:=Equivalence_Method6(DataLattice, EXT1, imgEXT2, ThePoint1, imgThePoint2);
    if TheEquiv<>false then
      return TheEquiv*Inverse(eBigMat);
    fi;
  od;
  return false;
end;



Periodic_StabilizerMethod6:=function(DataLattice, EXT, ThePoint)
  local TheStab, ListMatGens, nbMatch, eBigMat, imgThePoint, imgEXT, TheEquiv, eAddBigMat, GRP;
  TheStab:=Stabilizer_Method6(DataLattice, EXT, ThePoint);
  ListMatGens:=ShallowCopy(GeneratorsOfGroup(TheStab));
  nbMatch:=0;
  for eBigMat in DataLattice.TheComp.ListElement
  do
    imgThePoint:=ThePoint*eBigMat;
    imgEXT:=EXT*eBigMat;
    TheEquiv:=Equivalence_Method6(DataLattice, EXT, imgEXT, ThePoint, imgThePoint);
    if TheEquiv<>false then
      eAddBigMat:=Inverse(eBigMat);
      Add(ListMatGens, FuncExplodeBigMatrix(eAddBigMat).MatrixTransformation);
      nbMatch:=nbMatch+1;
    fi;
  od;
  GRP:=Group(ListMatGens);
  SetSize(GRP, nbMatch*Size(TheStab));
  return GRP;
end;





Periodic_TestEquivalenceOfDelaunay:=function(DataLattice, EXT1, EXT2, Delaunay1Stab)
  local CP1, CP2, TheCenter1, TheCenter2, n, DM1, DM2, test, ePerm, GRP1, REP, LFactors1, GroupDen;
  CP1:=CenterRadiusDelaunayPolytopeGeneral(DataLattice.GramMat, EXT1);
  TheCenter1:=CP1.Center;
  CP2:=CenterRadiusDelaunayPolytopeGeneral(DataLattice.GramMat, EXT2);
  TheCenter2:=CP2.Center;
  DM1:=DistanceMatrixDelaunay(DataLattice.GramMat, EXT1);
  DM2:=DistanceMatrixDelaunay(DataLattice.GramMat, EXT2);
  test:=IsIsomorphicEdgeColoredGraph(DM1, DM2);
  if test=false then
    return false;
  fi;
  ePerm:=PermList(test);
  GRP1:=Delaunay1Stab.PrivateInfo.GRP;
  GroupDen:=DataLattice.GroupDen;
  LFactors1:=FactorsInt(LcmInt(GroupDen, ListFactors(TheCenter1))/GroupDen);
  REP:=Periodic_EquivalenceMethod0(DataLattice, EXT1, EXT2, Delaunay1Stab, ePerm);
  if REP<>fail then
    return REP;
  else
    if DataLattice.IsMethod6ok then
      return Periodic_EquivalenceMethod6(DataLattice, EXT1, EXT2, TheCenter1, TheCenter2);
    fi;
    if DataLattice.n<=7 then
      return Periodic_EquivalenceMethod2(DataLattice, TheCenter1, TheCenter2);
    fi;
    if Order(GRP1)<=50000 then
      return Periodic_EquivalenceMethod4(DataLattice, EXT1, EXT2, GRP1, ePerm);
    fi;
    if Length(LFactors1)>2 then
      return Periodic_EquivalenceMethod3(DataLattice, TheCenter1, TheCenter2);
    fi;
    return Periodic_EquivalenceMethod2(DataLattice, TheCenter1, TheCenter2);
  fi;
end;


Periodic_StabilizerOfDelaunay:=function(DataLattice, EXT)
  local CP, TheCenter, n, DM, GRP, EasyCase, REP, TheReply, LFactors, GroupDen, HLR;
  CP:=CenterRadiusDelaunayPolytopeGeneral(DataLattice.GramMat, EXT);
  TheCenter:=CP.Center;
  DM:=DistanceMatrixDelaunay(DataLattice.GramMat, EXT);
  GRP:=AutomorphismGroupEdgeColoredGraph(DM);
  GroupDen:=DataLattice.GroupDen;
  LFactors:=FactorsInt(LcmInt(GroupDen, ListFactors(TheCenter))/GroupDen);
  REP:=Periodic_StabilizerMethod0(DataLattice, EXT, GRP);
  if REP<>fail then
    EasyCase:=true;
    TheReply:=REP;
  elif true then
    EasyCase:=false;
    if DataLattice.IsMethod6ok then
      TheReply:=Periodic_StabilizerMethod6(DataLattice, EXT, TheCenter);
    elif DataLattice.n<=8 then
      TheReply:=Periodic_StabilizerMethod2(DataLattice, TheCenter);
    elif Order(GRP)< 50000 then
      TheReply:=Periodic_StabilizerMethod4(DataLattice, EXT, GRP);
    elif Order(GRP)>10000000 then
      TheReply:=Periodic_StabilizerMethod2(DataLattice, TheCenter);
    elif Length(LFactors)>1 then
      TheReply:=Periodic_StabilizerMethod3(DataLattice, TheCenter);
    elif Order(GRP)<= 50000 then
      TheReply:=Periodic_StabilizerMethod4(DataLattice, EXT, GRP);
    else
      TheReply:=Periodic_StabilizerMethod3(DataLattice, TheCenter);
    fi;
  fi;
  HLR:=VertexRepresentationDelaunaySymmetry(TheReply, EXT, TheCenter);
  return rec(PrivateInfo:=rec(EasyCase:=EasyCase, GRP:=GRP),
             PermutationStabilizer:=HLR.PermutationStabilizer,
             PhiPermMat:=HLR.PhiPermMat);
end;


#
# element of ListCosetRed do not have a first 1.
# eVect do not have a first 1.
Periodic_ClosestVector:=function(GramMat, ListCosetRed, eVect)
  local n, ListSolution, ListNorm, eCos, reply, MinNorm, ListVectReturn, iCos;
  n:=Length(GramMat);
  ListSolution:=[];
  ListNorm:=[];
  for eCos in ListCosetRed
  do
    reply:=CVPVallentinProgram(GramMat, eVect-eCos);
    Add(ListSolution, reply.ListVect);
    Add(ListNorm, reply.TheNorm);
  od;
  MinNorm:=Minimum(ListNorm);
  ListVectReturn:=[];
  for iCos in [1..Length(ListCosetRed)]
  do
    if ListNorm[iCos]=MinNorm then
      Append(ListVectReturn, List(ListSolution[iCos], x->x+ListCosetRed[iCos]));
    fi;
  od;
  return rec(ListVect:=ListVectReturn, TheNorm:=MinNorm);
end;



Periodic_FindAdjacentDelaunayPolytope:=function(GramMat, ListCoset, EXT, ListInc)
  local n, IndependentBasis, TheFac, ListCosetRed, ListGraverOptions, i, eVect, ListMinRadius, ListSelectedVertex, eCos, eVal, iCol, xVal, reply, SelectedVertex, VSet, CP, MinRadius, NoOpt, NewCand, eGraver, pos, Vcent;
#  Print("Beginning of Periodic_FindAdjacentDelaunayPolytope\n");
  n:=Length(GramMat);
  IndependentBasis:=RowReduction(EXT{ListInc}, n).EXT;
  TheFac:=FindFacetInequality(EXT, ListInc);
  ListCosetRed:=List(ListCoset, x->x{[2..n+1]});
  ListGraverOptions:=[];
  for i in [1..n]
  do
    eVect:=ListWithIdenticalEntries(n+1,0);
    eVect[i+1]:=1;
    Add(ListGraverOptions, ShallowCopy(eVect));
    eVect[i+1]:=-1;
    Add(ListGraverOptions, ShallowCopy(eVect));
  od;
  ListMinRadius:=[];
  ListSelectedVertex:=[];
  for eCos in ListCoset
  do
    # first find a point on the right side
    iCol:=First([2..n+1], x->TheFac[x]<>0);
    eVect:=ListWithIdenticalEntries(n+1, 0);
    eVect[iCol]:=1;
    xVal:=0;
    while(true)
    do
      SelectedVertex:=eCos+xVal*eVect;
      if TheFac*SelectedVertex < 0 then
        break;
      fi;
      SelectedVertex:=eCos-xVal*eVect;
      if TheFac*SelectedVertex < 0 then
        break;
      fi;
      xVal:=xVal+1;
    od;
    VSet:=Concatenation(IndependentBasis, [SelectedVertex]);
    CP:=CenterRadiusDelaunayPolytopeGeneral(GramMat, VSet);
    MinRadius:=CP.SquareRadius;
    # then we iterate until we cannot do better
    while(true)
    do
      NoOpt:=true;
      for eGraver in ListGraverOptions
      do
        NewCand:=SelectedVertex+eGraver;
        VSet:=Concatenation(IndependentBasis, [SelectedVertex]);
        CP:=CenterRadiusDelaunayPolytopeGeneral(GramMat, VSet);
        if TheFac*NewCand < 0 then
          if CP.SquareRadius < MinRadius then
            NoOpt:=false;
            MinRadius:=CP.SquareRadius;
            SelectedVertex:=NewCand;
          fi;
        fi;
      od;
      if NoOpt=true then
        break;
      fi;
    od;
    Add(ListMinRadius, MinRadius);
    Add(ListSelectedVertex, SelectedVertex);
  od;
  MinRadius:=Minimum(ListMinRadius);
  pos:=Position(ListMinRadius, MinRadius);
  SelectedVertex:=ListSelectedVertex[pos];
  while(true)
  do
    VSet:=Concatenation(IndependentBasis, [SelectedVertex]);
    CP:=CenterRadiusDelaunayPolytopeGeneral(GramMat, VSet);
    Vcent:=CP.Center{[2..n+1]};
    reply:=Periodic_ClosestVector(GramMat, ListCosetRed, Vcent);
    if reply.TheNorm=CP.SquareRadius then
      break;
    else
      SelectedVertex:=Concatenation([1], reply.ListVect[1]);
    fi;
  od;
#  Print("   Ending of Periodic_FindAdjacentDelaunayPolytope\n");
  return List(reply.ListVect, x->Concatenation([1], x));
end;






Periodic_DelaunayInvariant:=function(DataLattice, EXT)
  local CP, LFactors, TheDet, DistInvariant, eIso, test, rnk;
  if Length(EXT) < 200 then
    DistInvariant:=SymmetricMatrixOccurences(DistanceMatrixDelaunay(DataLattice.GramMat, EXT));
  else
    DistInvariant:="undefined";
  fi;
  #
  CP:=CenterRadiusDelaunayPolytopeGeneral(DataLattice.GramMat, EXT);
  #
  eIso:=Isobarycenter(EXT);
  test:=eIso=CP.Center;
  #
#  need to think on adding this back or not
#  GroupDen:=GroupDenominators(DataLattice.MatrixGRP);
#  LFactors:=LcmInt(GroupDen, ListFactors(CP.Center))/GroupDen;
  #
  rnk:=RankMat(EXT);
  return rec(nbV:=Length(EXT), DistInvariant:=DistInvariant, RankMat:=rnk, Radius:=CP.SquareRadius, test:=test);
end;




Periodic_InitialDelaunayPolytope:=function(GramMat, ListCoset)
  local n, ListCosetRed, ListCosetDiff, ListRelevantPoints, i, V, DefiningInequality, TheRandomDirection, TheLP, eVect, TheNorm, TheCVP, ListInequalities, eEnt, RetEXT;
  Print("Beginning of Periodic_InitialDelaunayPolytope\n");
  n:=Length(GramMat);
  ListCosetRed:=List(ListCoset, x->x{[2..n+1]});
  ListCosetDiff:=List([1..Length(ListCosetRed)], x->ListCosetRed[x]-ListCosetRed[1]);
  # we translate the lattice so as to be able to find the Delaunay
  ListRelevantPoints:=[];
  for i in [1..n]
  do
    V:=ListWithIdenticalEntries(n,0);
    V[i]:=1;
    Add(ListRelevantPoints, ShallowCopy(V));
    V[i]:=-1;
    Add(ListRelevantPoints, ShallowCopy(V));
  od;
  DefiningInequality:=function(eVect)
    return Concatenation([eVect*GramMat*eVect/2], -eVect*GramMat);
  end;
  TheRandomDirection:=FuncRandomDirection(n, 10);
  while(true)
  do
    ListInequalities:=List(ListRelevantPoints, DefiningInequality);
    TheLP:=LinearProgramming(ListInequalities, TheRandomDirection);
    eVect:=ListWithIdenticalEntries(n,0);
    for eEnt in TheLP.primal_solution
    do
      eVect[eEnt[1]]:=eEnt[2];
    od;
    TheNorm:=eVect*GramMat*eVect;
    Print("TheNorm=", TheNorm, "\n");
    TheCVP:=Periodic_ClosestVector(GramMat, ListCosetDiff, eVect);
    if TheCVP.TheNorm=TheNorm then
      Print("Ending of Periodic_InitialDelaunayPolytope\n");
      RetEXT:=List(TheCVP.ListVect, x->Concatenation([1], x+ListCosetRed[1]));
      return RetEXT;
    fi;
    for eVect in TheCVP.ListVect
    do
      Add(ListRelevantPoints, eVect);
    od;
    Print("|ListRelevantPoints|=", Length(ListRelevantPoints), "\n");
  od;
end;


CrystallographicGroup:=function(GramMat, ListCoset)
  local n, eCos, ListCrystGens, ListPointGens, ProvPtGRP, FuncInsert, PtGRP, iCos, eMat, eTrans, eBigMat, IsOK, pos;
  n:=Length(GramMat);
  for eCos in ListCoset
  do
    if Length(eCos)<>n+1 then
      Error("Cosets should be of length n+1");
    fi;
    if eCos[1]<>1 then
      Error("Homogeneous coordinates: first coordinate should be 1");
    fi;
    if PeriodicVectorMod1(eCos)<>eCos then
      Error("The coset should be reduced modulo 1");
    fi;
  od;
  ListCrystGens:=[];
  ListPointGens:=[];
  ProvPtGRP:=Group([IdentityMat(n)]);
  FuncInsert:=function(eBigMat)
    local eMat, test;
    eMat:=FuncExplodeBigMatrix(eBigMat).MatrixTransformation;
    test:=eMat in ProvPtGRP;
    if test=false then
      Add(ListCrystGens, eBigMat);
      Add(ListPointGens, eMat);
      ProvPtGRP:=Group(ListPointGens);
    fi;
  end;
  PtGRP:=ArithmeticAutomorphismGroup([GramMat]);
  for eMat in PtGRP
  do
    for iCos in [1..Length(ListCoset)]
    do
      eTrans:=ListCoset[iCos]{[2..n+1]}-ListCoset[1]{[2..n+1]}*eMat;
      eBigMat:=FuncCreateBigMatrix(eTrans, eMat);
      IsOK:=true;
      for eCos in ListCoset
      do
        pos:=Position(ListCoset, PeriodicVectorMod1(eCos*eBigMat));
        if pos=fail then
          IsOK:=false;
        fi;
      od;
      if IsOK=true then
        FuncInsert(eBigMat);
      fi;
    od;
  od;
  return PersoGroupMatrix(ListCrystGens, n+1);
end;


RationalBaseIntMat:=function(TheMat)
  local Den, nbLine, nbCol, iLine, iCol;
  Den:=1;
  nbLine:=Length(TheMat);
  nbCol:=Length(TheMat[1]);
  for iLine in [1..nbLine]
  do
    for iCol in [1..nbCol]
    do
      Den:=LcmInt(Den, DenominatorRat(TheMat[iLine][iCol]));
    od;
  od;
  return BaseIntMat(Den*TheMat)/Den;
end;


GetTranslationGroup:=function(ListCoset)
  local n, ListCosetRed, TranslationMatrix, FuncInsert, iCos, jCos, eTrans, IsVectorOK, eCos, test;
  n:=Length(ListCoset[1])-1;
  ListCosetRed:=List(ListCoset, x->x{[2..n+1]});
  TranslationMatrix:=IdentityMat(n);
  FuncInsert:=function(eTrans)
    local eSol;
    eSol:=SolutionMat(TranslationMatrix, eTrans);
    if IsIntegralVector(eSol)=false then
      TranslationMatrix:=RationalBaseIntMat(Concatenation([eTrans],TranslationMatrix));
    fi;
  end;
  for iCos in [1..Length(ListCosetRed)-1]
  do
    for jCos in [iCos+1..Length(ListCosetRed)]
    do
      eTrans:=ListCosetRed[jCos]-ListCosetRed[iCos];
      IsVectorOK:=true;
      for eCos in ListCosetRed
      do
        test:=Position(ListCosetRed, VectorMod1(eTrans+eCos));
        if test=fail then
          IsVectorOK:=false;
        fi;
      od;
      if IsVectorOK=true then
        FuncInsert(eTrans);
      fi;
    od;
  od;
  return TranslationMatrix;
end;

IsOnlyIntegralTranslations:=function(ListCoset)
  local TranslationMatrix;
  TranslationMatrix:=GetTranslationGroup(ListCoset);
  if IsIntegralMat(TranslationMatrix)=true then
    return true;
  else
    return false;
  fi;
end;


CosetChecking:=function(ListCoset, GramMat)
  local n, eCos;
  n:=Length(GramMat);
  if Length(Set(ListCoset))<>Length(ListCoset) then
    Error("There is repetition in the list of cosets");
  fi;
  for eCos in ListCoset
  do
    if Length(eCos)<>n+1 then
      Error("Cosets should be of length n+1");
    fi;
    if eCos[1]<>1 then
      Error("Homogeneous coordinates: first coordinate should be 1");
    fi;
    if PeriodicVectorMod1(eCos)<>eCos then
      Print("The coset should be reduced modulo 1\n");
      Print("i.e. it should be ", PeriodicVectorMod1(eCos), "\n");
      Print("instead of ", eCos, "\n");
      Error("Please correct");
    fi;
  od;
end;



ForKernel_Periodic_DataLatticePolyhedralDatabase:=function(GramMat, MatrixGRP, ListCoset, ThePrefix, IsSaving)
  local n, ListMatrGens, ListPointGens, PointGRP, ListPermGens, PermGRP, phi, FuncRawImage, TestBelonging, DataLattice, FindAdjacentDelaunay, FindDelaunay, eCos, IsBankSave, IsRespawn, FuncStabilizer, FuncIsomorphy, DataPolyhedral, DelaunayDatabase, PathTMP, PathSAVE, PathPermanent, TheReply, FuncInvariant, eBigMat, eMat, FuncEquiv, FuncAutom, GroupDen, MyOption, FuncLatticeAutomorphism, FuncLatticeIsomorphism, TheInvariantBase, WorkingAffineBasis, TheComp, IsMethod6ok, TheZero, ZeroStabilizer, GramMatGrp, ListPermCosets, GroupCoset, eList, eGen, ListCosetRed, FindClosestElement, KillingDelaunay, KillingAdjacency;
  n:=Length(GramMat);
  CosetChecking(ListCoset, GramMat);
  ListCosetRed:=List(ListCoset, x->x{[2..n+1]});
  if IsOnlyIntegralTranslations(ListCoset)=false then
    Error("The only translation symmetry authorized are integral");
  fi;
  ListPermCosets:=[];
  for eGen in GeneratorsOfGroup(MatrixGRP)
  do
    eList:=List(ListCoset,x->Position(ListCoset,PeriodicVectorMod1(x*eGen)));
    Add(ListPermCosets, PermList(eList));
  od;
  GroupCoset:=Group(ListPermCosets);
  GroupDen:=GroupDenominators(MatrixGRP);
  if IsPositiveDefiniteSymmetricMatrix(GramMat)=false then
    Error("The matrix should be positive definite");
  fi;
  ListMatrGens:=GeneratorsOfGroup(MatrixGRP);
  ListPointGens:=List(ListMatrGens, x->FuncExplodeBigMatrix(x).MatrixTransformation);
  PointGRP:=Group(ListPointGens);
  for eMat in ListPointGens
  do
    if eMat*GramMat*TransposedMat(eMat)<>GramMat then
      Print("The point group of the crystallographic group\n");
      Print("  does not leave invariant the Gram matrix\n");
      Error("Please correct");
    fi;
  od;
  FuncInvariant:=function(EXT)
    return Periodic_DelaunayInvariant(rec(GramMat:=GramMat), EXT);
  end;
  ListPermGens:=__ExtractInvariantFaithfulFamilyShortVector(GramMat, PointGRP).ListPermGens;
  PermGRP:=Group(ListPermGens);
  phi:=GroupHomomorphismByImagesNC(PermGRP, PointGRP, ListPermGens, ListPointGens);
  FuncRawImage:=function(ePointMat)
    local nbGen, f, hom, hom2;
    nbGen:=Length(ListMatrGens);
    f:=FreeGroup(nbGen);
    hom:=GroupHomomorphismByImagesNC(f, PointGRP, GeneratorsOfGroup(f), ListPointGens);
    hom2:=GroupHomomorphismByImagesNC(f, MatrixGRP, GeneratorsOfGroup(f), ListMatrGens);
    return Image(hom2, PreImagesRepresentative(hom, ePointMat));
  end;
  FindAdjacentDelaunay:=function(EXT, eSet)
    return Periodic_FindAdjacentDelaunayPolytope(GramMat, ListCoset, EXT, eSet);
  end;
  FindClosestElement:=function(eVect)
    return Periodic_ClosestVector(GramMat, ListCosetRed, eVect);
  end;
  FuncEquiv:=function(EXT1, EXT2, ThePoint1, ThePoint2)
    local LFactors1;
    LFactors1:=FactorsInt(LcmInt(GroupDen, ListFactors(ThePoint1))/GroupDen);
    if IsMethod6ok=true then
      return Periodic_EquivalenceMethod6(DataLattice, EXT1, EXT2, ThePoint1, ThePoint2);
    fi;
    if n<=8 then
      return Periodic_EquivalenceMethod2(DataLattice, ThePoint1, ThePoint2);
    elif Length(LFactors1)>1 then
      return Periodic_EquivalenceMethod3(DataLattice, ThePoint1, ThePoint2);
    else
      return Periodic_EquivalenceMethod2(DataLattice, ThePoint1, ThePoint2);
    fi;
  end;
  FuncAutom:=function(EXT, ThePoint)
    local LFactors, TheGRP, RedPoint, MatrixGens, eMat, eTrans, GRPret;
    LFactors:=FactorsInt(LcmInt(GroupDen, ListFactors(ThePoint))/GroupDen);
    if IsMethod6ok=true then
      TheGRP:=Periodic_StabilizerMethod6(DataLattice, EXT, ThePoint);
    elif n<=8 then
      TheGRP:=Periodic_StabilizerMethod2(DataLattice, ThePoint);
    elif Length(LFactors)>1 then
      TheGRP:=Periodic_StabilizerMethod3(DataLattice, ThePoint);
    else
      TheGRP:=Periodic_StabilizerMethod2(DataLattice, ThePoint);
    fi;
    RedPoint:=ThePoint{[2..n+1]};
    MatrixGens:=[];
    for eMat in GeneratorsOfGroup(TheGRP)
    do
      eTrans:=RedPoint-RedPoint*eMat;
      Add(MatrixGens, FuncCreateBigMatrix(eTrans, eMat));
    od;
    GRPret:=Group(MatrixGens);
    SetSize(GRPret, Size(TheGRP));
    return GRPret;
  end;
  FindDelaunay:=function()
    return Periodic_InitialDelaunayPolytope(GramMat, ListCoset);
  end;
  TestBelonging:=function(eBigMat)
    local eMat, eCos;
    eMat:=FuncExplodeBigMatrix(eBigMat).MatrixTransformation;
    if IsIntegralMat(eMat)=false then
      return false;
    fi;
    for eCos in ListCoset
    do
      if Position(ListCoset, PeriodicVectorMod1(eCos*eBigMat))=fail then
        return false;
      fi;
    od;
    return true;
  end;
  TheInvariantBase:=__ExtractInvariantZBasisShortVector(GramMat, PointGRP);
#  this is because AUTO/ISOM do not stomach non integral vectors.
#  TheInvariantBase:=[];
  Print("|TheInvariantBase|=", Length(TheInvariantBase), "\n");
  if DoesItContainStandardBasis(TheInvariantBase)=true then
    WorkingAffineBasis:=IdentityMat(n);
  else
    # if there is no affine basis, then the situation would be very hard
    WorkingAffineBasis:=CreateAffineBasis(TheInvariantBase);
  fi;
  MyOption:="";
  FuncLatticeAutomorphism:=function(ListMat, SVR, AffBas)
    return ArithmeticAutomorphismMatrixFamily_Nauty(ListMat, SVR);
#    return ArithmeticAutomorphismMatrixFamily_HackSouvignier(MyOption, ListMat, SVR, AffBas);
  end;
  FuncLatticeIsomorphism:=function(ListMat1, SVR1, AffBas1, ListMat2, SVR2, AffBas2)
    return ArithmeticEquivalenceMatrixFamily_Nauty(ListMat1, SVR1, ListMat2, SVR2);
#    return ArithmeticEquivalenceMatrixFamily_HackSouvignier(MyOption, ListMat1, SVR1, AffBas1, ListMat2, SVR2, AffBas2);
  end;
  KillingDelaunay:=function(EXT)
    return false;
  end;
  KillingAdjacency:=function(EXT1, EXT2)
    return false;
  end;
  #
  #
  PathTMP:=Concatenation(ThePrefix, "Tmp/");
  PathSAVE:=Concatenation(ThePrefix, "PolyhedralSave/");
  PathPermanent:=Concatenation(ThePrefix, "Saving/");
  Exec("mkdir -p ", PathTMP);
  Exec("mkdir -p ", PathSAVE);
  Exec("mkdir -p ", PathPermanent);
  #
  #
  DataLattice:=rec(
    n:=n,
    GramMat:=GramMat,
    PermGRP:=PermGRP, phi:=phi,
    ListMatrGens:=ListMatrGens,
    NeedAffBas:=true,
    MatrixGRP:=MatrixGRP,
    PointGRP:=PointGRP,
    ListCoset:=ListCoset,
    GroupCoset:=GroupCoset,
    PathPermanent:=PathPermanent,
    Saving:=IsSaving,
    KillingDelaunay:=KillingDelaunay,
    KillingAdjacency:=KillingAdjacency,
    FindDelaunayPolytope:=FindDelaunay,
    GroupDen:=GroupDen,
    FuncEquiv:=FuncEquiv,
    FuncAutom:=FuncAutom,
    FuncInvariant:=Periodic_DelaunayInvariant,
    FuncLatticeAutomorphism:=FuncLatticeAutomorphism,
    FuncLatticeIsomorphism:=FuncLatticeIsomorphism,
    FindAdjacentDelaunay:=FindAdjacentDelaunay,
    FindClosestElement:=FindClosestElement,
    FuncStabilizerDelaunay:=Periodic_StabilizerOfDelaunay,
    FuncIsomorphismDelaunay:=Periodic_TestEquivalenceOfDelaunay,
    InvariantBase:=TheInvariantBase,
    AffBas:=WorkingAffineBasis,
    TestBelonging:=TestBelonging);
  TheZero:=ListWithIdenticalEntries(n+1,0);
  TheZero[1]:=1;
  ZeroStabilizer:=Periodic_StabilizerMethod2(DataLattice, TheZero);
  GramMatGrp:=ArithmeticAutomorphismGroup([GramMat]);
  if Order(GramMatGrp)=Order(ZeroStabilizer) then
    IsMethod6ok:=true;
    TheComp:=OrbitWithAction(MatrixGRP, TheZero, PeriodicOnClassesMod1);
  else
    IsMethod6ok:=false;
    TheComp:="irrelevant";
  fi;
  DataLattice.IsMethod6ok:=IsMethod6ok;
  DataLattice.TheComp:=TheComp;
  #
  #
  FuncStabilizer:=function(EXT)
    local DM;
    if Length(EXT) < 30 then
      return Group(());
    fi;
    DM:=DistanceMatrixDelaunay(GramMat, EXT);
    return AutomorphismGroupEdgeColoredGraph(DM);
  end;
  FuncIsomorphy:=function(EXT1, EXT2)
    local DM1, DM2, test;
    if Length(EXT1)<>Length(EXT2) then
      return false;
    fi;
    DM1:=DistanceMatrixDelaunay(GramMat, EXT1);
    DM2:=DistanceMatrixDelaunay(GramMat, EXT2);
    test:=IsIsomorphicEdgeColoredGraph(DM1, DM2);
    if test=false then
      return false;
    else
      return PermList(test);
    fi;
  end;
  #
  #
  IsRespawn:=function(OrdGRP, EXT, TheDepth)
    if Length(EXT)>=90 then
      return true;
    fi;
    if TheDepth>=2 then
      return false;
    fi;
    if OrdGRP<=6000 then
      return false;
    fi;
    if Length(EXT)<=36 then
      return false;
    fi;
    return true;
  end;
  IsBankSave:=function(EllapsedTime, OrdGRP, EXT, TheDepth)
    if TheDepth=0 then
      return false;
    fi;
    if EllapsedTime>=600 then
      return true;
    fi;
    if Length(EXT)<=30 then
      return false;
    fi;
    return true;
  end;
  DataPolyhedral:=rec(IsBankSave:=IsBankSave,
    TheDepth:=0,
    IsRespawn:=IsRespawn,
    ThePath:=PathTMP,
    Saving:=IsSaving,
    GetInitialRays:=GetInitialRays_LinProg,
    ThePathSave:=PathSAVE,
    FuncInvariant:=FuncInvariant,
    DualDescriptionFunction:=poly_private@DualDescriptionLRS_Reduction,
    ProjectionLiftingFramework:=__ProjectionLiftingFramework,
    FuncStabilizer:=FuncStabilizer,
    FuncIsomorphy:=FuncIsomorphy,
    GroupFormalism:=OnSetsGroupFormalism(500));
  DelaunayDatabase:=DelaunayDatabaseManagement(PathPermanent, IsSaving, false);
  return rec(DataLattice:=DataLattice, DataPolyhedral:=DataPolyhedral, DelaunayDatabase:=DelaunayDatabase);
end;


Periodic_DelaunayDescriptionStandardKernel:=function(TheGramMat, MatrixGRP, ListCoset, ThePrefix, IsSaving, KillingDelaunay, KillingAdjacency)
  local DLPD, TheReply;
  DLPD:=ForKernel_Periodic_DataLatticePolyhedralDatabase(TheGramMat, MatrixGRP, ListCoset, ThePrefix, IsSaving);
  DLPD.DataLattice.KillingDelaunay:=KillingDelaunay;
  DLPD.DataLattice.KillingAdjacency:=KillingAdjacency;
  TheReply:=ComputeDelaunayDecomposition(DLPD.DataLattice, DLPD.DataPolyhedral, DLPD.DelaunayDatabase);
  Print("TheReply=", TheReply, "\n");
  if TheReply="all was ok" then
    return DLPD.DelaunayDatabase.FuncReturnCompleteDescription();
  else
    return TheReply;
  fi;
end;

Periodic_DelaunayDescriptionStandard:=function(TheGramMat, MatrixGRP, ListCoset)
  local ThePrefix, IsSaving, KillingDelaunay, KillingAdjacency;
  # we decided to remove the IsTotalGroup thing
  # because it causes huge slowdown.
  KillingDelaunay:=function(EXT)
    return false;
  end;
  KillingAdjacency:=function(EXT1, EXT2)
    return false;
  end;
  ThePrefix:=Filename(POLYHEDRAL_tmpdir, "DualDesc/");
  Exec("mkdir -p ", ThePrefix);
  IsSaving:=false;
  #
  return Periodic_DelaunayDescriptionStandardKernel(TheGramMat, MatrixGRP, ListCoset, ThePrefix, IsSaving, KillingDelaunay, KillingAdjacency);
end;






StabilizerOfDelaunayHighDimMethod6:=function(DataLattice, EXT)
  local CP, TheCenter, TheReply, HLR;
  CP:=CenterRadiusDelaunayPolytopeGeneral(DataLattice.GramMat, EXT);
  TheCenter:=CP.Center;
  TheReply:=Stabilizer_Method6(DataLattice, EXT, TheCenter);
  HLR:=VertexRepresentationDelaunaySymmetry(TheReply, EXT, TheCenter);
  return rec(PermutationStabilizer:=HLR.PermutationStabilizer,
             PhiPermMat:=HLR.PhiPermMat);
end;


TestEquivalenceOfDelaunayHighDimMethod6:=function(DataLattice, EXT1, EXT2, Delaunay1Stab)
  local CP1, CP2, TheCenter1, TheCenter2, eEquiv;
  #
  CP1:=CenterRadiusDelaunayPolytopeGeneral(DataLattice.GramMat, EXT1);
  TheCenter1:=CP1.Center;
  CP2:=CenterRadiusDelaunayPolytopeGeneral(DataLattice.GramMat, EXT2);
  TheCenter2:=CP2.Center;
  eEquiv:=Equivalence_Method6(DataLattice, EXT1, EXT2, TheCenter1, TheCenter2);
  if eEquiv=false then
    return false;
  fi;
  if TheCenter1*eEquiv<>TheCenter2 then
    Error("We have a big problem in that place, please debug");
  fi;
  return eEquiv;
end;





StabilizerOfDelaunayPureNauty:=function(DataLattice, EXT)
  local CP, TheCenter, n, DM, GRP, EasyCase, REP, TheReply, LFactors, HLR;
  TheCenter:=Isobarycenter(EXT);
  DM:=DistanceMatrixDelaunay(DataLattice.GramMat, EXT);
  GRP:=AutomorphismGroupEdgeColoredGraph(DM);
  LFactors:=FactorsInt(ListFactors(TheCenter));
  Print("  |Isom|=", Order(GRP), "\n");
  REP:=Stabilizer_Method0(DataLattice, EXT, GRP);
  if REP<>fail then
    EasyCase:=true;
    TheReply:=REP;
  else
    EasyCase:=false;
    TheReply:=Stabilizer_Method4(DataLattice, EXT, GRP);
  fi;
  HLR:=VertexRepresentationDelaunaySymmetry(TheReply, EXT, TheCenter);
  return rec(PrivateInfo:=rec(EasyCase:=EasyCase, GRP:=GRP),
             PermutationStabilizer:=HLR.PermutationStabilizer,
             PhiPermMat:=HLR.PhiPermMat);
end;


TestEquivalenceOfDelaunayPureNauty:=function(DataLattice, EXT1, EXT2, Delaunay1Stab)
  local n, DM1, DM2, test, ePerm, GRP1, REP, LFactors1, TheQuot;
  DM1:=DistanceMatrixDelaunay(DataLattice.GramMat, EXT1);
  DM2:=DistanceMatrixDelaunay(DataLattice.GramMat, EXT2);
  test:=IsIsomorphicEdgeColoredGraph(DM1, DM2);
  if test=false then
    return false;
  fi;
  ePerm:=PermList(test);
  GRP1:=Delaunay1Stab.PrivateInfo.GRP;
  Print("|V|=", Length(EXT1));
  Print("  |LattIsom|=", Order(Delaunay1Stab.PermutationStabilizer));
  Print("  |Isom|=", Order(GRP1));
  Print("\n");
  #
  REP:=Equivalence_Method0(DataLattice, EXT1, EXT2, Delaunay1Stab, ePerm);
  if REP<>fail then
    return REP;
  else
    TheQuot:=Order(GRP1)/Order(Delaunay1Stab.PermutationStabilizer);
    if TheQuot< 10 then
      return Equivalence_Method5(DataLattice, EXT1, EXT2, Delaunay1Stab, ePerm);
    fi;
    if TheQuot<=50000 then
      return Equivalence_Method4(DataLattice, EXT1, EXT2, GRP1, ePerm);
    fi;
    if TheQuot< 100 then
      return Equivalence_Method5(DataLattice, EXT1, EXT2, Delaunay1Stab, ePerm);
    fi;
    return Equivalence_Method4(DataLattice, EXT1, EXT2, GRP1, ePerm);
  fi;
end;






ForKernel_PureNauty_DataLatticePolyhedralDatabase:=function(TheGramMat, ThePrefix, IsSaving, MaximalMemorySave)
  local n, eGen, IsRespawn, IsBankSave, PathTMP, PathSAVE, DataPolyhedral, DataLattice, PathPermanent, FuncStabilizer, FuncIsomorphy, DelaunayDatabase, TestBelonging, ListPermGens, MatrGens, PermGRP, phi, FindDelaunay, FindAdjacentDelaunay, TheReply, FuncInvariant;
  n:=Length(TheGramMat);
  FindAdjacentDelaunay:=function(EXT, eOrb)
    return FindAdjacentDelaunayPolytope(TheGramMat, EXT, eOrb);
  end;
  if ThePrefix[Length(ThePrefix)]<>'/' then
    Error("Last character of ThePrefix=", ThePrefix, " should be /");
  fi;
  #
  #
  # We assumed the group to be the total group
  # If not then do double cosets operations
  TestBelonging:=function(eBigMat)
    local eMat;
    eMat:=FuncExplodeBigMatrix(eBigMat).MatrixTransformation;
    return IsIntegralMat(eMat);
  end;
  #
  #
  FuncStabilizer:=function(EXT)
    local DM;
    DM:=DistanceMatrixDelaunay(TheGramMat, EXT);
    return AutomorphismGroupEdgeColoredGraph(DM);
  end;
  FuncIsomorphy:=function(EXT1, EXT2)
    local DM1, DM2, test;
    DM1:=DistanceMatrixDelaunay(TheGramMat, EXT1);
    DM2:=DistanceMatrixDelaunay(TheGramMat, EXT2);
    test:=IsIsomorphicEdgeColoredGraph(DM1, DM2);
    if test=false then
      return false;
    else
      return PermList(test);
    fi;
  end;
  FuncInvariant:=function(EXT)
    return DelaunayInvariantLattice(rec(GramMat:=TheGramMat), EXT);
  end;
  #
  #
  IsRespawn:=function(OrdGRP, EXT, TheDepth)
    if Length(EXT)>=60 then
      return true;
    fi;
    if TheDepth>=2 then
      return false;
    fi;
    if OrdGRP<=6000 then
      return false;
    fi;
    if Length(EXT)<=36 then
      return false;
    fi;
    return true;
  end;
  IsBankSave:=function(EllapsedTime, OrdGRP, EXT, TheDepth)
    if TheDepth=0 then
      return false;
    fi;
    if EllapsedTime>=600 then
      return true;
    fi;
    if Length(EXT)<=30 then
      return false;
    fi;
    return true;
  end;
  FindDelaunay:=function()
    return FindDelaunayPolytope(TheGramMat);
  end;
  PathTMP:=Concatenation(ThePrefix, "tmp/");
  Exec("mkdir -p ", PathTMP);
  if IsSaving=true then
    PathSAVE:=Concatenation(ThePrefix, "PolyhedralSave/");
    PathPermanent:=Concatenation(ThePrefix, "Saving/");
    Exec("mkdir -p ", PathSAVE);
    Exec("mkdir -p ", PathPermanent);
  else
    PathSAVE:="/irrelevant/";
    PathPermanent:="/irrelevant/";
  fi;
  DataPolyhedral:=rec(IsBankSave:=IsBankSave,
    TheDepth:=0,
    IsRespawn:=IsRespawn,
    ThePath:=PathTMP,
    Saving:=IsSaving,
    GetInitialRays:=GetInitialRays_LinProg,
    ThePathSave:=PathSAVE,
    DualDescriptionFunction:=poly_private@DualDescriptionLRS_Reduction,
    ProjectionLiftingFramework:=__ProjectionLiftingFramework,
    FuncStabilizer:=FuncStabilizer,
    FuncIsomorphy:=FuncIsomorphy,
    FuncInvariant:=FuncInvariant,
    GroupFormalism:=OnSetsGroupFormalismDelaunay(rec(GramMat:=TheGramMat)));
  Exec("mkdir -p ", PathTMP);
  Exec("mkdir -p ", PathSAVE);
  DataLattice:=rec(Saving:=IsSaving,
                   PathPermanent:=PathPermanent,
                   GramMat:=TheGramMat,
                   NeedAffBas:=false,
                   n:=Length(TheGramMat),
                   FuncStabilizerDelaunay:=StabilizerOfDelaunayPureNauty,
                   FuncIsomorphismDelaunay:=TestEquivalenceOfDelaunayPureNauty,
                   FindDelaunayPolytope:=FindDelaunay,
                   FuncInvariant:=DelaunayInvariantLattice,
                   TestBelonging:=TestBelonging,
                   FindAdjacentDelaunay:=FindAdjacentDelaunay);
  DelaunayDatabase:=DelaunayDatabaseManagement(PathPermanent, IsSaving, MaximalMemorySave);
  return rec(DataLattice:=DataLattice, DataPolyhedral:=DataPolyhedral, DelaunayDatabase:=DelaunayDatabase);
end;





DelaunayDescription_PureNauty_StandardKernel:=function(TheGramMat, ThePrefix, IsSaving, KillingDelaunay, KillingAdjacency, FileInformation, MaximalMemorySave)
  local output, DLPD, TheReply;
  DLPD:=ForKernel_PureNauty_DataLatticePolyhedralDatabase(TheGramMat, ThePrefix, IsSaving, MaximalMemorySave);
  DLPD.DataLattice.KillingDelaunay:=KillingDelaunay;
  DLPD.DataLattice.KillingAdjacency:=KillingAdjacency;
  TheReply:=ComputeDelaunayDecomposition(DLPD.DataLattice, DLPD.DataPolyhedral, DLPD.DelaunayDatabase);
  if TheReply="all was ok" then
    output:=OutputTextFile(FileInformation, true);
    RadiusesAndDelaunayCenterDistances(output, DLPD.DelaunayDatabase, DLPD.DataLattice);
    CloseStream(output);
    return DLPD.DelaunayDatabase.FuncReturnCompleteDescription();
  else
    return TheReply;
  fi;
end;



GetBasis:=function(DataLattice, EXT)
  local n, CP, TheBasis, SpaceBas, iExt, eDiff, eDiffRed, eVect;
  CP:=CenterRadiusDelaunayPolytopeGeneral(DataLattice.GramMat, EXT);
  n:=DataLattice.n;
  TheBasis:=[];
  Add(TheBasis, CP.Center);
  SpaceBas:=[];
  for iExt in [1..Length(EXT)]
  do
    eDiff:=EXT[iExt]-EXT[1];
    eDiffRed:=eDiff{[2..n+1]};
    Add(SpaceBas, eDiffRed);
  od;
  for eVect in NullspaceIntMat(DataLattice.GramMat*TransposedMat(RemoveFractionMatrix(SpaceBas)))
  do
    Add(TheBasis, Concatenation([0], eVect));
  od;
  return TheBasis;
end;

#
# return the list of Delaunay polytopes containing EXT
# starting from the Delaunay OneRecord
SoftComputation:=function(DataLattice, DelaunayDatabase, EXT, StabEXT, OneRecord)
  local n, ListRecord, ListStatus, ListAdditionalInfo, FuncInsertRecord, OrdStabEXT, NumberIncident, SumElement, TheBarycenter, IsFinished, iRecord, eRecord, TheEXT, TheAdjacencies, DStabEXT, TheCenter, SingleInv, ListOrbitRelFacet, eAdjacency, StabBig, eDCS, eElt, fInc, TheEXT2, eG2, eSet2, TheBasis, TheStab;
  n:=DataLattice.n;
  ListRecord:=[OneRecord];
  ListStatus:=["NO"];
  ListAdditionalInfo:=[];
  FuncInsertRecord:=function(TheRecord)
    local eSingleRecord, TheStab, g;
    for eSingleRecord in ListRecord
    do
      if eSingleRecord.iOrb=TheRecord.iOrb then
        TheStab:=DelaunayDatabase.FuncDelaunayGetGroup(TheRecord.iOrb);
        g:=RepresentativeAction(TheStab.PermutationStabilizer, eSingleRecord.eSet, TheRecord.eSet, OnSets);
        if g<>fail then
          return;
        fi;
      fi;
    od;
    Add(ListStatus, "NO");
    Add(ListRecord, TheRecord);
  end;
  OrdStabEXT:=Size(StabEXT);
  NumberIncident:=0;
  SumElement:=ListWithIdenticalEntries(n+1, 0);
  while(true)
  do
    IsFinished:=true;
    for iRecord in [1..Length(ListRecord)]
    do
      eRecord:=ListRecord[iRecord];
      if ListStatus[iRecord]="NO" then
        IsFinished:=false;
        TheEXT:=DelaunayDatabase.FuncDelaunayGetEXT(eRecord.iOrb);
        TheAdjacencies:=DelaunayDatabase.FuncDelaunayGetAdjacencies(eRecord.iOrb);
        TheStab:=DelaunayDatabase.FuncDelaunayGetGroup(eRecord.iOrb);
        DStabEXT:=Stabilizer(TheStab.PermutationStabilizer, eRecord.eSet, OnSets);
        NumberIncident:=NumberIncident+OrdStabEXT/Size(DStabEXT);
        TheCenter:=CenterRadiusDelaunayPolytopeGeneral(DataLattice.GramMat, TheEXT).Center*eRecord.eMat;
        SingleInv:=OrbitBarycenter(TheCenter, StabEXT);
        SumElement:=SumElement+(OrdStabEXT/Size(DStabEXT))*SingleInv.TheBarycenter;
        ListOrbitRelFacet:=[];
        for eAdjacency in TheAdjacencies
        do
          StabBig:=Stabilizer(TheStab.PermutationStabilizer, eAdjacency.eInc, OnSets);
          for eDCS in DoubleCosets(TheStab.PermutationStabilizer, StabBig, DStabEXT)
          do
            eElt:=Representative(eDCS);
            fInc:=OnSets(eAdjacency.eInc, eElt);
            if IsSubset(fInc, eRecord.eSet) then
              Add(ListOrbitRelFacet, fInc);
              TheEXT2:=DelaunayDatabase.FuncDelaunayGetEXT(eAdjacency.iDelaunay);
              eG2:=eAdjacency.eBigMat*Image(TheStab.PhiPermMat, eElt)*eRecord.eMat;
              eSet2:=Set(List(EXT, x->Position(TheEXT2*eG2, x)));
              FuncInsertRecord(rec(iOrb:=eAdjacency.iDelaunay, eMat:=eG2, eSet:=eSet2));
            fi;
          od;
        od;
        ListStatus[iRecord]:="YES";
        ListAdditionalInfo[iRecord]:=rec(Stab:=DStabEXT, ListOrbitRelFacet:=ListOrbitRelFacet);
      fi;
    od;
    if IsFinished=true then
      break;
    fi;
  od;
  TheBasis:=GetBasis(DataLattice, EXT);
  return rec(EXT:=EXT,
             ListRecord:=ListRecord,
             TheBasis:=TheBasis,
             eInvariant:=DelaunayInvariantLattice(rec(GramMat:=DataLattice.GramMat), EXT),
             ListAdditionalInfo:=ListAdditionalInfo,
             NumberIncident:=NumberIncident,
             TheBarycenter:=SumElement/NumberIncident);
end;


VoronoiPolytopeListVertices:=function(DataLattice, DelaunayDatabase, StabEXT, SoftComp)
  local ListVert, eSoft, TheEXT, eCenter;
  ListVert:=[];
  for eSoft in SoftComp.ListRecord
  do
    TheEXT:=DelaunayDatabase.FuncDelaunayGetEXT(eSoft.iOrb);
    eCenter:=CenterRadiusDelaunayPolytopeGeneral(DataLattice.GramMat, TheEXT).Center*eSoft.eMat;
    Append(ListVert, Orbit(StabEXT, eCenter, OnPoints));
  od;
  return ListVert;
end;



SCV_GetOrbitVertices:=function(DataLattice, DelaunayDatabase)
  local n, ListOrbit, nbOrb, iOrb, TheStab, EXT, O, eO, eStabPermVert, TheTrans, eBigMat, eRep, TheRecordVerticesVoronoi, ListListStabVert, ListListOriginVert, ListListFACset, ListStabVert, ListFACset, TheFACset, OriginsVert, ListOriginVert, eIso, fIso, eSingVert, eGen, ListPermGens, eList, iAdj, eAdj, ListAdj, nbAdj, eSet, nbO, iO, ListListSingVert, ListSingVert, ListListFACineq, ListFACineq, TheFACineq, EXTrelevant, eIneq, ListListStabFac, NewListGens, eStabPermFac, ListStabFac, ListListOriginFac, ListOriginFac, OriginsFac;
  n:=DataLattice.n;
  ListOrbit:=[];
  nbOrb:=DelaunayDatabase.FuncDelaunayGetNumber();
  ListListFACset:=[];
  ListListFACineq:=[];
  ListListOriginVert:=[];
  ListListOriginFac:=[];
  ListListStabVert:=[];
  ListListStabFac:=[];
  ListListSingVert:=[];
  for iOrb in [1..nbOrb]
  do
    ListFACset:=[];
    ListFACineq:=[];
    ListOriginFac:=[];
    ListStabVert:=[];
    ListStabFac:=[];
    ListSingVert:=[];
    TheStab:=DelaunayDatabase.FuncDelaunayGetGroup(iOrb);
    EXT:=DelaunayDatabase.FuncDelaunayGetEXT(iOrb);
    ListOriginVert:=ListWithIdenticalEntries(Length(EXT), 0);
    O:=Orbits(TheStab.PermutationStabilizer, [1..Length(EXT)], OnPoints);
    ListAdj:=DelaunayDatabase.FuncDelaunayGetAdjacencies(iOrb);
    nbAdj:=Length(ListAdj);
    nbO:=Length(O);
    for iO in [1..nbO]
    do
      eO:=O[iO];
      eSingVert:=eO[1];
      ListOriginVert{eO}:=ListWithIdenticalEntries(Length(eO), iO);
      eStabPermVert:=Stabilizer(TheStab.PermutationStabilizer, eSingVert, OnPoints);
      Add(ListStabVert, eStabPermVert);
      TheTrans:=-EXT[eSingVert]{[2..n+1]};
      eBigMat:=FuncCreateBigMatrix(TheTrans, IdentityMat(n));
      EXTrelevant:=EXT*eBigMat;
      Add(ListSingVert, eSingVert);
      TheFACset:=[];
      TheFACineq:=[];
      OriginsFac:=[];
      for iAdj in [1..nbAdj]
      do
        eAdj:=ListAdj[iAdj];
        for eSet in Orbit(TheStab.PermutationStabilizer, eAdj.eInc, OnSets)
        do
          if Position(eSet, eSingVert)<>fail then
            Add(TheFACset, eSet);
            eIneq:=FindFacetInequality(EXT, eSet);
            Add(TheFACineq, eIneq);
            Add(OriginsFac, iAdj);
          fi;
        od;
      od;
      Add(ListFACset, TheFACset);
      NewListGens:=[];
      for eGen in GeneratorsOfGroup(eStabPermVert)
      do
        eList:=List(TheFACset, x->Position(TheFACset, OnSets(x, eGen)));
        Add(NewListGens, PermList(eList));
      od;
      eStabPermFac:=PersoGroupPerm(NewListGens);
      Add(ListStabFac, eStabPermFac);
      Add(ListFACineq, TheFACineq);
      Add(ListOriginFac, OriginsFac);
      eIso:=Isobarycenter(EXTrelevant);
      fIso:=(Isobarycenter(EXTrelevant) + EXTrelevant[eSingVert])/2;
      eRep:=rec(k:=0,
                eIso:=eIso,
                fIso:=fIso,
                RelevantEXT:=EXTrelevant,
                ListOrbit:=[rec(iOrb:=iOrb,
                                iO:=iO,
                                eSetFac:=[],
                                eSetVert:=[1..Length(EXT)],
                                eBigMat:=eBigMat)]);
      Add(ListOrbit, eRep);
    od;
    Add(ListListFACset, ListFACset);
    Add(ListListFACineq, ListFACineq);
    Add(ListListOriginVert, ListOriginVert);
    Add(ListListOriginFac, ListOriginFac);
    Add(ListListStabVert, ListStabVert);
    Add(ListListStabFac, ListStabFac);
    Add(ListListSingVert, ListSingVert);
  od;
  TheRecordVerticesVoronoi:=rec(ListListFACset:=ListListFACset,
        ListListFACineq:=ListListFACineq,
        ListListOriginVert:=ListListOriginVert,
        ListListOriginFac:=ListListOriginFac,
        ListListStabVert:=ListListStabVert,
        ListListSingVert:=ListListSingVert,
        ListListStabFac:=ListListStabFac);
  return rec(ListOrbit:=ListOrbit, TheRecordVerticesVoronoi:=TheRecordVerticesVoronoi);
end;


OrbitsSecure:=function(TheGRP, TheSet, TheAct)
  local ListOrbits, TheSetWork, eElt, TheOrb;
  ListOrbits:=[];
  TheSetWork:=Set(List(TheSet, x->x));
  while(true)
  do
    if Length(TheSetWork)=0 then
      return ListOrbits;
    fi;
    eElt:=TheSetWork[1];
    TheOrb:=Set(Orbit(TheGRP, eElt, TheAct));
    if IsSubset(TheSetWork, TheOrb)=false then
      Error("We fail the inclusion test");
    fi;
    Add(ListOrbits, TheOrb);
    TheSetWork:=Difference(TheSetWork, TheOrb);
  od;
end;





#
#
# The goal is given a face of the Voronoi of dimension k
# to find the faces of dimension k+1 containing it.
SCV_Iteration:=function(DataLattice, DelaunayDatabase, TheRecordVerticesVoronoi, eRecord)
  local n, GramMat, EXT, TheListOrb, eOrbit, ListOrbitReturn, TheStab, ListFACset, ListFACineq, eIso, fIso, eNewRep, ListOrbit, ListIsobarycenter, ListStatus, TheNewRec, IsFinished, iOrb, iO, TheFACset, ListIncidentEXT, iCell, nbCell, FuncInsert, eStabPermFac, eStabPermFacB, TheMatrixGroup, ListAdj, eMatAdjEquiv1, eMatAdjEquiv2, iOrbitAdj, eSetVertAdj, eSetFacAdj, EXTimage, EXT2, iOriginVert, iOriginFac, idxFac, eMatEquiv, ePermEquiv, eFacRep, ListContainedFAC, Ofac, eStabFaceVert, eSetVert, eStabVert, eOfac, eSingVert, eVertCan, TheFACsetAdj, pos, iSingVert, eSetFac, TheStabAdj, ePermEquiv2, eMatEquiv2, eVertAdj, IsOKvert, EXTimage2, eSetVertOrb, RankIncidentEXT, kDimension, ListIsoCell, ListCP;
  n:=DataLattice.n;
  GramMat:=DataLattice.GramMat;
  TheStab:=DelaunayDatabase.FuncDelaunayGetGroup(eRecord.iOrb);
  EXT:=DelaunayDatabase.FuncDelaunayGetEXT(eRecord.iOrb);
  ListFACset:=TheRecordVerticesVoronoi.ListListFACset[eRecord.iOrb][eRecord.iO];
  ListFACineq:=TheRecordVerticesVoronoi.ListListFACineq[eRecord.iOrb][eRecord.iO];
  eStabPermFac:=TheRecordVerticesVoronoi.ListListStabFac[eRecord.iOrb][eRecord.iO];
  eStabPermFacB:=Stabilizer(eStabPermFac, eRecord.eSetFac, OnSets);
  TheListOrb:=SPAN_face_ExtremeRay(eRecord.eSetFac, eStabPermFacB, ListFACineq, EXT);
  kDimension:=n+1 - RankMat(EXT{eRecord.eSetVert});
  ListOrbitReturn:=[];
  iSingVert:=TheRecordVerticesVoronoi.ListListSingVert[eRecord.iOrb][eRecord.iO];
  eSingVert:=EXT[iSingVert]*eRecord.eBigMat;
  for eOrbit in TheListOrb
  do
    IsOKvert:=function(TheSetFac, eVert)
      local eFac;
      for eFac in TheSetFac
      do
        if Position(eFac, eVert)=fail then
          return false;
        fi;
      od;
      return true;
    end;
    eSetVertOrb:=Filtered([1..Length(EXT)], x->IsOKvert(ListFACset{eOrbit}, x));
    ListIncidentEXT:=EXT{eSetVertOrb}*eRecord.eBigMat;
    eIso:=Isobarycenter(ListIncidentEXT);
    fIso:=(eIso + eSingVert)/2;
    eNewRep:=rec(iOrb:=eRecord.iOrb,
                  iO:=eRecord.iO,
                  eSetFac:=eOrbit,
                  eSetVert:=eSetVertOrb,
                  eBigMat:=eRecord.eBigMat);
    ListOrbit:=[];
    ListIsoCell:=[];
    ListCP:=[];
    ListIsobarycenter:=[];
    ListStatus:=[];
    FuncInsert:=function(eNewRep)
      local EXT, EXTimg, eIso, fIso, gIso, iOrbit, eEquiv, CP;
      EXT:=DelaunayDatabase.FuncDelaunayGetEXT(eNewRep.iOrb);
      EXTimg:=EXT*eNewRep.eBigMat;
      if Position(EXTimg, eSingVert)<>TheRecordVerticesVoronoi.ListListSingVert[eNewRep.iOrb][eNewRep.iO] then
        Error("Inconsistency over vertices");
      fi;
      if Set(EXTimg{eNewRep.eSetVert})<>Set(ListIncidentEXT) then
        Error("Inconsistency that needs to be resolved");
      fi;
      gIso:=(eSingVert + Isobarycenter(EXTimg) + Isobarycenter(EXTimg{eNewRep.eSetVert}))/3;
      for iOrbit in [1..Length(ListOrbit)]
      do
        eEquiv:=DataLattice.FuncEquiv(ListIncidentEXT, ListIncidentEXT, gIso, ListIsobarycenter[iOrbit]);
        if eEquiv<>false then
          return;
        fi;
#        if gIso=ListIsobarycenter[iOrbit] then
#          return;
#        fi;
      od;
      CP:=CenterRadiusDelaunayPolytopeGeneral(GramMat, EXTimg);
      Add(ListOrbit, eNewRep);
      Add(ListIsobarycenter, gIso);
      Add(ListStatus, "NO");
      Add(ListIsoCell, Isobarycenter(EXT));
      Add(ListCP, CP.Center);
    end;
    FuncInsert(eNewRep);
    while(true)
    do
      IsFinished:=true;
      nbCell:=Length(ListOrbit);
      for iCell in [1..nbCell]
      do
        if ListStatus[iCell]="NO" then
          IsFinished:=false;
          ListStatus[iCell]:="YES";
          iOrb:=ListOrbit[iCell].iOrb;
          iO:=ListOrbit[iCell].iO;
          TheStab:=DelaunayDatabase.FuncDelaunayGetGroup(iOrb);
          ListAdj:=DelaunayDatabase.FuncDelaunayGetAdjacencies(iOrb);
          TheFACset:=TheRecordVerticesVoronoi.ListListFACset[iOrb][iO];
          eStabVert:=TheRecordVerticesVoronoi.ListListStabVert[iOrb][iO];
          eSetVert:=ListOrbit[iCell].eSetVert;
          eSetFac:=ListOrbit[iCell].eSetFac;
          eStabFaceVert:=Stabilizer(eStabVert, eSetVert, OnSets);
          ListContainedFAC:=TheFACset{eSetFac};
          Ofac:=OrbitsSecure(eStabFaceVert, ListContainedFAC, OnSets);
#          Ofac:=List(ListContainedFAC, x->[x]);
          for eOfac in Ofac
          do
            eFacRep:=eOfac[1];
            idxFac:=Position(TheFACset, eFacRep);
            iOriginFac:=TheRecordVerticesVoronoi.ListListOriginFac[iOrb][iO][idxFac];
            iOrbitAdj:=ListAdj[iOriginFac].iDelaunay;
            ePermEquiv:=RepresentativeAction(TheStab.PermutationStabilizer, ListAdj[iOriginFac].eInc, eFacRep, OnSets);
            eMatEquiv:=Image(TheStab.PhiPermMat, ePermEquiv);
            eMatAdjEquiv1:=ListAdj[iOriginFac].eBigMat*eMatEquiv*ListOrbit[iCell].eBigMat;
            EXT2:=DelaunayDatabase.FuncDelaunayGetEXT(iOrbitAdj);
            EXTimage:=EXT2*eMatAdjEquiv1;
            pos:=Position(EXTimage, eSingVert);
            iOriginVert:=TheRecordVerticesVoronoi.ListListOriginVert[iOrbitAdj][pos];
            eVertAdj:=TheRecordVerticesVoronoi.ListListSingVert[iOrbitAdj][iOriginVert];
            TheStabAdj:=DelaunayDatabase.FuncDelaunayGetGroup(iOrbitAdj);
            ePermEquiv2:=RepresentativeAction(TheStabAdj.PermutationStabilizer, eVertAdj, pos, OnPoints);
            eMatEquiv2:=Image(TheStabAdj.PhiPermMat, ePermEquiv2);
            eMatAdjEquiv2:=eMatEquiv2*eMatAdjEquiv1;
            EXTimage2:=EXT2*eMatAdjEquiv2;
            eSetVertAdj:=Set(List(ListIncidentEXT, x->Position(EXTimage2, x)));
            if Position(eSetVertAdj, fail)<>fail then
              Error("We have some inconsistency in eSetVertAdj");
            fi;
            TheFACsetAdj:=TheRecordVerticesVoronoi.ListListFACset[iOrbitAdj][iOriginVert];
            eSetFacAdj:=Filtered([1..Length(TheFACsetAdj)], x->IsSubset(TheFACsetAdj[x], eSetVertAdj));
            eNewRep:=rec(iOrb:=iOrbitAdj, iO:=iOriginVert, eSetFac:=eSetFacAdj, eSetVert:=eSetVertAdj, eBigMat:=eMatAdjEquiv2);
            FuncInsert(eNewRep);
          od;
        fi;
      od;
      if IsFinished=true then
        break;
      fi;
    od;
    TheNewRec:=rec(k:=kDimension+1,
                   eIso:=eIso,
                   fIso:=fIso,
                   RelevantEXT:=ListIncidentEXT,
                   SingVert:=eSingVert,
                   ListIsoCell:=ListIsoCell,
                   ListCP:=ListCP,
                   ListOrbit:=ListOrbit);
    Add(ListOrbitReturn, TheNewRec);
  od;
  return ListOrbitReturn;
end;






SCV_EnumerationStronglyTransversal:=function(DataLattice, DelaunayDatabase, BeltFreeInformations)
  local GramMat, n, InitComp, ListListOrbits, NewListOrbit, FuncInsert, lFaceGen, lFace, ListFoundStrongTrans, nbFreeVect, i, TheGeneration, eNewFace, TheInitList, eFace, ReturnListListOrbit, OneListOrbit, EXTvoronoiFace, EXTiso, TheNewRec, TheStab, TheStabMatr, CP, EXT, eDelOrbit, eOrbit, eListOrbit, rnk, TheMat, testCent, FreeInformations, GRPpermFreeVect, ListFreeVectors, eSymbol, SoftComp, StabEXT, eIso, GetSumFace, GetStronglyTransversalSignature, GetInformationSuperSumVoronoiFreeZonotope, ListFoundPos, ListFoundNeg, iFreeVect, eRecPN, ListFoundZero, eVectZ, eScal, eVectAdj, eVectRed, iRank, ListEXTdelaunay, eRelevantEXT, ListSingVertices, eSingIdx, eRecOrbit;
  Print("Doing enumeration of strongly transversal faces\n");
  GramMat:=DataLattice.GramMat;
  n:=DataLattice.n;
  FreeInformations:=BeltFreeInformations.FuncGetAllFreeVectors();
  GRPpermFreeVect:=FreeInformations.PermGRPfree;
  ListFreeVectors:=FreeInformations.ListFreeVect;
  nbFreeVect:=Length(ListFreeVectors);
  GetStronglyTransversalSignature:=function(OneFace, eFreeVect)
    local eRecord, iOrb, iO, EXT, eSingVert, eVert, nbP, nbN, eVect, eScal, eSingIdx, EXTtotal, fRecord, EXTsel, eSingIdxSel, eSingVertSel;
    eRecord:=OneFace.ListOrbit[1];
    iOrb:=eRecord.iOrb;
    iO:=eRecord.iO;
    EXT:=DelaunayDatabase.FuncDelaunayGetEXT(iOrb)*eRecord.eBigMat;
    EXTtotal:=EXT{eRecord.eSetVert};
    eSingIdx:=InitComp.TheRecordVerticesVoronoi.ListListSingVert[iOrb][iO];
    eSingVert:=EXT[eSingIdx];
    for fRecord in OneFace.ListOrbit
    do
      EXTsel:=DelaunayDatabase.FuncDelaunayGetEXT(fRecord.iOrb)*fRecord.eBigMat;
      eSingIdxSel:=InitComp.TheRecordVerticesVoronoi.ListListSingVert[fRecord.iOrb][fRecord.iO];
      eSingVertSel:=EXTsel[eSingIdxSel];
      if Set(EXTsel{fRecord.eSetVert})<>Set(EXTtotal) then
        Error("We found inconsistencies in OneFace.ListOrbit");
      fi;
      if eSingVertSel<>eSingVert then
        Error("We found inconsistencies in eSingVert");
      fi;
    od;
    nbP:=0;
    nbN:=0;
    for eVert in Difference(EXTtotal, [eSingVert])
    do
      eVect:=eVert{[2..n+1]} - eSingVert{[2..n+1]};
      eScal:=eVect*GramMat*eFreeVect;
      if eScal > 0 then
        nbP:=nbP+1;
      fi;
      if eScal < 0 then
        nbN:=nbN+1;
      fi;
    od;
    return rec(nbP:=nbP, nbN:=nbN);
  end;
  InitComp:=SCV_GetOrbitVertices(DataLattice, DelaunayDatabase);
  TheInitList:=[];
  for eFace in InitComp.ListOrbit
  do
    ListFoundStrongTrans:=[];
    ListFoundPos:=[];
    ListFoundNeg:=[];
    ListFoundZero:=[];
    for iFreeVect in [1..nbFreeVect]
    do
      eRecPN:=GetStronglyTransversalSignature(eFace, ListFreeVectors[iFreeVect]);
      if eRecPN.nbP > 0 and eRecPN.nbN > 0 then
        Add(ListFoundStrongTrans, iFreeVect);
      elif eRecPN.nbP > 0 then
        Add(ListFoundPos, iFreeVect);
      elif eRecPN.nbN > 0 then
        Add(ListFoundNeg, iFreeVect);
      else
        Add(ListFoundZero, iFreeVect);
      fi;
    od;
    if Length(ListFoundStrongTrans) > 0 then
      eNewFace:=rec(eFace:=eFace, ListStrongTrans:=ListFoundStrongTrans, ListFoundPos:=ListFoundPos, ListFoundNeg:=ListFoundNeg, ListFoundZero:=ListFoundZero);
      Add(TheInitList, eNewFace);
    fi;
  od;
  ListListOrbits:=[TheInitList];
  for i in [1..n-2]
  do
    NewListOrbit:=[];
    FuncInsert:=function(OneNewCase)
      local eCase, eEquiv;
      for eCase in NewListOrbit
      do
        eEquiv:=DataLattice.FuncEquiv(eCase.eFace.RelevantEXT, OneNewCase.eFace.RelevantEXT, eCase.eFace.fIso, OneNewCase.eFace.fIso);
        if eEquiv<>false then
          return;
        fi;
      od;
      Add(NewListOrbit, OneNewCase);
    end;
    for lFace in ListListOrbits[i]
    do
      TheGeneration:=SCV_Iteration(DataLattice, DelaunayDatabase, InitComp.TheRecordVerticesVoronoi, lFace.eFace.ListOrbit[1]);
      for lFaceGen in TheGeneration
      do
        ListFoundStrongTrans:=[];
        ListFoundPos:=[];
        ListFoundNeg:=[];
        ListFoundZero:=[];
        for iFreeVect in [1..nbFreeVect]
        do
          eRecPN:=GetStronglyTransversalSignature(lFaceGen, ListFreeVectors[iFreeVect]);
          if eRecPN.nbP > 0 and eRecPN.nbN > 0 then
            Add(ListFoundStrongTrans, iFreeVect);
          elif eRecPN.nbP > 0 then
            Add(ListFoundPos, iFreeVect);
          elif eRecPN.nbN > 0 then
            Add(ListFoundNeg, iFreeVect);
          else
            Add(ListFoundZero, iFreeVect);
          fi;
        od;
        if Length(ListFoundStrongTrans) > 0 then
          eNewFace:=rec(eFace:=lFaceGen, ListStrongTrans:=ListFoundStrongTrans, ListFoundPos:=ListFoundPos, ListFoundNeg:=ListFoundNeg, ListFoundZero:=ListFoundZero);
          FuncInsert(eNewFace);
        fi;
      od;
    od;
    Print("i=", i, " |NewListOrbits|=", Length(NewListOrbit), "\n");
    Add(ListListOrbits, NewListOrbit);
  od;
  ReturnListListOrbit:=[];
  Print("|ListListOrbits|=", Length(ListListOrbits), "\n");
  for iRank in [0..n-2]
  do
    eListOrbit:=ListListOrbits[iRank+1];
    OneListOrbit:=[];
    Print("  Treating |eListOrbit|=", Length(eListOrbit), "\n");
    for eOrbit in eListOrbit
    do
      EXTvoronoiFace:=[];
      TheStabMatr:=DataLattice.FuncAutom(eOrbit.eFace.RelevantEXT, eOrbit.eFace.fIso);
      ListEXTdelaunay:=[];
      ListSingVertices:=[];
      eRelevantEXT:=eOrbit.eFace.RelevantEXT;
      for eDelOrbit in eOrbit.eFace.ListOrbit
      do
        EXT:=DelaunayDatabase.FuncDelaunayGetEXT(eDelOrbit.iOrb)*eDelOrbit.eBigMat;
        eSingIdx:=InitComp.TheRecordVerticesVoronoi.ListListSingVert[eDelOrbit.iOrb][eDelOrbit.iO];
        Add(ListSingVertices, EXT[eSingIdx]);
        if Set(eRelevantEXT)<>Set(EXT{eDelOrbit.eSetVert}) then
          Error("We have some error");
        fi;
        Add(ListEXTdelaunay, Set(EXT{eDelOrbit.eSetVert}));
        CP:=CenterRadiusDelaunayPolytopeGeneral(GramMat, EXT);
        Append(EXTvoronoiFace, Orbit(TheStabMatr, CP.Center, OnPoints));
      od;
      if Length(Set(ListEXTdelaunay))<>1 then
        Error("ListEXTdelaunay is not correct");
      fi;
      Print("rnkDelaunay=", RankMat(ListEXTdelaunay[1]), " rnkVoronoi=", RankMat(EXTvoronoiFace), "\n");
      if RankMat(ListEXTdelaunay[1]) + RankMat(EXTvoronoiFace)<>n+2 then
        Error("The orthogonal decomposition does not hold");
      fi;
      EXTiso:=Isobarycenter(EXTvoronoiFace);
      if RankMat(EXTvoronoiFace)<>iRank+1 then
        Error("Rank consistency error");
      fi;
      TheMat:=Concatenation(EXTvoronoiFace, List(eOrbit.ListStrongTrans, x->Concatenation([0], ListFreeVectors[x])));
      rnk:=RankMat(TheMat);
      testCent:=IsCentrallySymmetric(EXTvoronoiFace);
      TheNewRec:=rec(k:=eOrbit.eFace.k,
                     eIso:=eOrbit.eFace.eIso,
                     fIso:=eOrbit.eFace.fIso,
                     RelevantEXT:=eOrbit.eFace.RelevantEXT,
                     ListOrbit:=eOrbit.eFace.ListOrbit,
                     EXTiso:=EXTiso,
                     testCent:=testCent,
                     EXTvoronoiFace:=EXTvoronoiFace,
                     ListStrongTrans:=eOrbit.ListStrongTrans,
                     ListFoundPos:=eOrbit.ListFoundPos,
                     ListFoundNeg:=eOrbit.ListFoundNeg,
                     ListFoundZero:=eOrbit.ListFoundZero,
                     rnk:=rnk);
      Add(OneListOrbit, TheNewRec);
    od;
    Add(ReturnListListOrbit, OneListOrbit);
  od;
  #adding the facets as .... facet generating
  OneListOrbit:=[];
  eRecOrbit:=BeltFreeInformations.GetBelt_Equivariant();
  for eSymbol in eRecOrbit.ListOrbit1
  do
    EXT:=eSymbol.EXT;
    StabEXT:=eSymbol.StabEXT;
    SoftComp:=SoftComputation(DataLattice, DelaunayDatabase, EXT, StabEXT, eSymbol.TheDel);
    EXTvoronoiFace:=VoronoiPolytopeListVertices(DataLattice, DelaunayDatabase, StabEXT, SoftComp);
    testCent:=IsCentrallySymmetric(EXTvoronoiFace);
    eIso:=Isobarycenter(EXT);
    ListFoundStrongTrans:=[];
    ListFoundPos:=[];
    ListFoundNeg:=[];
    ListFoundZero:=[];
    for iFreeVect in [1..nbFreeVect]
    do
      eVectZ:=Concatenation([1], ListWithIdenticalEntries(n,0));
      eVectAdj:=Difference(Set(EXT), [eVectZ])[1];
      eVectRed:=eVectAdj{[2..n+1]};
      eScal:=eVectRed*GramMat*ListFreeVectors[iFreeVect];
      if eScal > 0 then
        Add(ListFoundPos, iFreeVect);
      elif eScal < 0 then
        Add(ListFoundNeg, iFreeVect);
      else
        Add(ListFoundZero, iFreeVect);
      fi;
    od;
    TheNewRec:=rec(k:=n-1,
                   eIso:=eIso,
                   RelevantEXT:=EXT,
                   ListOrbit:="unset at present",
                   testCent:=testCent,
                   EXTvoronoiFace:=EXTvoronoiFace,
                   EXTiso:=Isobarycenter(EXTvoronoiFace),
                   ListStrongTrans:=[],
                   ListFoundPos:=ListFoundPos,
                   ListFoundNeg:=ListFoundNeg,
                   ListFoundZero:=ListFoundZero,
                   rnk:=n);
    Add(OneListOrbit, TheNewRec);
  od;
  Add(ReturnListListOrbit, OneListOrbit);
  #
  GetSumFace:=function(eOrb)
    local iFreeVect, ListVectPositif, ListVectZonotop, ListEXT, eFreeVect, eRecPN, eSumPositif, EXTface, EXTrank, rnk, ListIncidentNonOrient, ListIncidentOrient, eScal;
    ListVectPositif:=[];
    ListVectZonotop:=[];
    ListEXT:=[];
    EXTrank:=[];
    ListIncidentNonOrient:=[];
    ListIncidentOrient:=[];
    for iFreeVect in [1..nbFreeVect]
    do
      eFreeVect:=ListFreeVectors[iFreeVect];
      eRecPN:=GetStronglyTransversalSignature(eOrb, eFreeVect);
      if eRecPN.nbP>0 and eRecPN.nbN>0 then
        Add(ListEXT, [eFreeVect, -eFreeVect]);
        eScal:=eOrb.eIso*GramMat*eFreeVect;
        if eScal=0 then
          Add(ListIncidentNonOrient, eFreeVect);
        else
          if eScal>0 then
            Add(ListIncidentOrient, eFreeVect);
          else
            Add(ListIncidentOrient, -eFreeVect);
          fi;
        fi;
        Add(EXTrank, Concatenation([0], eFreeVect));
      fi;
      if eRecPN.nbP>0 then
        Add(ListVectPositif, eFreeVect);
      elif eRecPN.nbN>0 then
        Add(ListVectPositif, -eFreeVect);
      fi;
    od;
    eSumPositif:=Sum(ListVectPositif);
    EXTface:=List(eOrb.EXTvoronoiFace, x->x{[2..n+1]});
    Append(EXTrank, eOrb.EXTvoronoiFace);
    Add(ListEXT, EXTface);
    rnk:=RankMat(EXTrank);
    return rec(ListEXT:=ListEXT,
               ListIncidentNonOrient:=ListIncidentNonOrient,
               ListIncidentOrient:=ListIncidentOrient,
               rnk:=rnk,
               eSumPositif:=eSumPositif);
  end;
  GetInformationSuperSumVoronoiFreeZonotope:=function()
    local EXT, FuncInsert, i, eOrb, TheSumEXT, eEXT, ListSumEXT, nbOrbitFace, ListOrbit, eSet, TheStab, TheStabRed, eList, ListPermGens, ListListOrbitSubset, ListOrbitSubset, eSumEXT, eGen, PermGRP, iOrbit, ListBelt, EXTface, rnk, iOrb, nbOrb, eSingleVert, FuncInsertFace, eRecSum, ListOrb, GRPperm, eIsoSum, eInversion, EXTsumP, EXTsum, StrategyFullDim1, StrategyFullDim2;
    EXT:=[];
    FuncInsert:=function(eEXT)
      local pos;
      pos:=Position(EXT, eEXT);
      if pos<>fail then
        return;
      fi;
      Append(EXT, Orbit(DataLattice.PointGRP, eEXT, OnPoints));
    end;
    ListSumEXT:=[];
    FuncInsertFace:=function(EXT)
      local eEXT;
      Add(ListSumEXT, EXT);
      for eEXT in EXT
      do
        FuncInsert(eEXT);
      od;
    end;
    StrategyFullDim1:=function(eRecSum, TheStab)
      local EXTsum, EXTsumP, ListPermGens, eGen, eList, eIsoSum, eInversion, GRPperm, ListOrbFac, eOrbFac, eStab, eCent1, eCent2, eDiff, eScal, TheSumEXT, fOrbFac, hOrbFac;
      EXTsum:=MINKSum_Generic(eRecSum.ListEXT);
      EXTsumP:=List(EXTsum, x->Concatenation([1], x));
      ListPermGens:=[];
      for eGen in GeneratorsOfGroup(TheStab)
      do
        eList:=List(EXTsumP, x->Position(EXTsumP, x*eGen));
        Add(ListPermGens, PermList(eList));
      od;
      eIsoSum:=Isobarycenter(EXTsumP);
      eList:=List(EXTsumP, x->Position(EXTsumP, 2*eIsoSum-x));
      eInversion:=PermList(eList);
      Add(ListPermGens, eInversion);
      GRPperm:=Group(ListPermGens);
      ListOrbFac:=DualDescriptionStandard(EXTsumP, GRPperm);
      for eOrbFac in ListOrbFac
      do
        eStab:=Stabilizer(GRPperm, eOrbFac, OnSets);
        Print("|eOrbFac|=", Length(eOrbFac), " |Stab|=", Order(eStab), "\n");
        eCent1:=Isobarycenter(EXTsumP{eOrbFac});
        fOrbFac:=OnSets(eOrbFac, eInversion);
        eCent2:=Isobarycenter(EXTsumP{fOrbFac});
        eDiff:=eCent2{[2..n+1]}-eCent1{[2..n+1]};
        eScal:=eDiff*GramMat*eOrb.eIso{[2..n+1]};
        if eScal=0 then
          Error("We are in trouble somehow");
        else
          if eScal>0 then
            hOrbFac:=fOrbFac;
          else
            hOrbFac:=eOrbFac;
          fi;
        fi;
        TheSumEXT:=List(EXTsumP{hOrbFac}, x->x+Concatenation([0], eRecSum.eSumPositif));
        Print("  |TheSumEXT|=", Length(TheSumEXT), "\n");
        FuncInsertFace(TheSumEXT);
      od;
    end;
    StrategyFullDim2:=function(eRecSum, TheStab)
      local BoundingSet, ListPermGens, eGen, eSmallGen, eList, GRPray, eSetSelect, ListOrbFac, eOrbFac, EXTsum, EXTsumP, TheSumEXT, ListVect;
      if i<>0 then
        return fail;
      fi;
      if Length(eRecSum.ListIncidentNonOrient)>0 then
        return fail;
      fi;
      BoundingSet:=[];
      ListPermGens:=[];
      for eGen in GeneratorsOfGroup(TheStab)
      do
        eSmallGen:=FuncExplodeBigMatrix(eGen);
        eList:=List(eRecSum.ListIncidentOrient, x->Position(eRecSum.ListIncidentOrient, x*eSmallGen));
        Add(ListPermGens, PermList(eList));
      od;
      GRPray:=Group(ListPermGens);
      ListVect:=eRecSum.ListIncidentOrient;
      eSetSelect:=EliminationByRedundancyEquivariant(ListVect, BoundingSet, GRPray).eSetSelect;
      if Length(eSetSelect)<>Length(ListVect) then
        return fail;
      fi;
      ListOrbFac:=DualDescription(ListVect, GRPray);
      for eOrbFac in ListOrbFac
      do
        EXTsum:=MINKSum_Generic(ListVect{eOrbFac});
        EXTsumP:=List(EXTsum, x->Concatenation([1], x));
        TheSumEXT:=List(EXTsumP, x->x+Concatenation([0], eRecSum.eSumPositif));
        Print("  |TheSumEXT|=", Length(TheSumEXT), "\n");
        FuncInsertFace(TheSumEXT);
      od;
    end;
    for i in [0..n]
    do
      Print("i=", i, "\n");
      nbOrb:=Length(ReturnListListOrbit[i+1]);
      for iOrb in [1..nbOrb]
      do
        eOrb:=ReturnListListOrbit[i+1][iOrb];
        eRecSum:=GetSumFace(eOrb);
        eSingleVert:=eOrb.EXTvoronoiFace[1];
        Print("  iOrb=", iOrb, "/", nbOrb, " |ListEXT|=", Length(eRecSum.ListEXT), " rnk=", eRecSum.rnk, "\n");
        if eRecSum.rnk=n then
          Print("First case: the minkowski sum is only a facet\n");
          EXTsum:=MINKSum_Generic(eRecSum.ListEXT);
          EXTsumP:=List(EXTsum, x->Concatenation([1], x));
          Print("   found |EXTsumP|=", Length(EXTsumP), "\n");
          TheSumEXT:=List(EXTsumP, x->x+Concatenation([0], eRecSum.eSumPositif));
          FuncInsertFace(TheSumEXT);
        elif eRecSum.rnk=n+1 then
          Print("Second case: the minkowski sum is full dimensional.\n");
          Print("  Hence, we need to find the facets.\n");
          TheStab:=DataLattice.FuncAutom(eOrb.RelevantEXT, eOrb.eIso);
          Print(" |TheStab|=", Order(TheStab), "\n");
          StrategyFullDim1(eRecSum, TheStab);
        else
          Print("Third case: the sum is too low dimensional to be significant\n");
        fi;
      od;
    od;
    Print("|EXT|=", Length(EXT), "\n");
    nbOrbitFace:=Length(ListSumEXT);
    ListOrbit:=[];
    for eSumEXT in ListSumEXT
    do
      eSet:=List(eSumEXT, x->Position(EXT, x));
      Add(ListOrbit, eSet);
    od;
    ListPermGens:=[];
    for eGen in GeneratorsOfGroup(DataLattice.MatrixGRP)
    do
      eList:=List(EXT, x->Position(EXT, x*eGen));
      Add(ListPermGens, PermList(eList));
    od;
    PermGRP:=Group(ListPermGens);
    ListListOrbitSubset:=[];
    for iOrbit in [1..nbOrbitFace]
    do
      eSet:=ListOrbit[iOrbit];
      TheStab:=Stabilizer(PermGRP, eSet, OnSets);
      TheStabRed:=SecondReduceGroupAction(TheStab, eSet);
      EXTface:=EXT{eSet};
      ListOrbitSubset:=DualDescriptionStandard(EXTface, TheStabRed);
      Add(ListListOrbitSubset, ListOrbitSubset);
    od;
    ListBelt:=KernelBeltComputation(EXT, PermGRP, ListOrbit, ListListOrbitSubset);
    return rec(EXT:=EXT,
               ListOrbit:=ListOrbit,
               ListListOrbitSubset:=ListListOrbitSubset,
               ListBelt:=ListBelt);
  end;
  return rec(ReturnListListOrbit:=ReturnListListOrbit,
             GetInformationSuperSumVoronoiFreeZonotope:=GetInformationSuperSumVoronoiFreeZonotope);
end;

#
# We have a fixed rank, we want to find the minimal forbidden subsets
# for having rank TheMaxRank
FreedomStructure_GetFixedSubrank:=function(EXTvoronoiFace, ListStrongTrans, ListFreeVectors, GRPperm, TheMaxRank)
  local eStab, eStabRed, KillingFunction, nbVect, ListMaximal, TheEXTred, ListReturn, FuncInsert, eSet, ListReturnIso;
  eStab:=Stabilizer(GRPperm, ListStrongTrans, OnSets);
  eStabRed:=SecondReduceGroupAction(eStab, ListStrongTrans);
  TheEXTred:=RowReduction(EXTvoronoiFace).EXT;
  KillingFunction:=function(eSet)
    local EXTappend, rnk;
    EXTappend:=Concatenation(TheEXTred, List(eSet, x->Concatenation([0],ListFreeVectors[ListStrongTrans[x]])));
    rnk:=RankMat(EXTappend);
    if rnk > TheMaxRank+1 then
      return true;
    fi;
    if rnk < Length(TheEXTred) + Length(eSet) then
      return true;
    fi;
    return false;
  end;
#  EXT:=BuildSet(5, [0,1]);
#  EXT2:=Filtered(EXT, x->Sum(x) mod 2=0);
#  EXT3:=List(EXT2, x->Concatenation([1], x));
  nbVect:=Length(ListStrongTrans);
  ListMaximal:=MyEnumerationMaximal(nbVect, eStabRed, KillingFunction);
  Print("FS_GetFixedSubrank, |ListMaximal|=", Length(ListMaximal), "\n");
  Print("FS_GetFixedSubrank, TheMaxRank=", TheMaxRank, " |GRPperm|=", Order(GRPperm), "\n");
  Print("FS_GetFixedSubrank, |eStab|=", Order(eStab), " |eStabRed|=", Order(eStabRed), "\n");
  Print("FS_GetFixedSubrank, ListLen=", List(ListMaximal, Length), "\n");
  ListReturn:=List(ListMaximal, x->ListStrongTrans{x});
  ListReturnIso:=[];
  FuncInsert:=function(eSet)
    local fSet, test, rnk;
    for fSet in ListReturnIso
    do
      test:=RepresentativeAction(GRPperm, eSet, fSet, OnSets);
      if test<>fail then
        return;
      fi;
    od;
    rnk:=RankMat(ListFreeVectors{eSet});
    Print("rnk=", rnk, "\n");
    Add(ListReturnIso, eSet);
  end;
  for eSet in ListMaximal
  do
    FuncInsert(ListStrongTrans{eSet});
  od;
  return ListReturn;
end;





FreedomStructure_TestConfiguration_NextGeneration:=function(DataLattice, ListListStrongTrans, FreeInformations, ListRelevantVector, eSetInput)
  local eMatrixGRP, n, ListFreeVect, FuncGetPermutation, ListPermGens, ListMatrGens, eBigGen, eGen, ePerm, PermGRPfree, phi, i, eOrbit, eCent, eRecO, len, ListFreeVectTot, phiTot, ListPermGensTot, ePermTot, PermGRPfreeTot, eElt, eEltImg1, eEltImg2, ListVectorTrans, iPos, eImg1, eImg2, EXTcomplete, EXTdesc, nbOrbit, iOrbit, ListVectZon, ListVectZonAdd, eSetFace, ListOrbitFacetsInc, eFaceEXT, EXTsum, ListOrbitClusterFacet, ListEXT, eVect, eVectExt, EXTtot, ListPermGensEXT, eList, ListBelt, PermGRPext, eVectTrans, eVectTransSum, preEXTsum, eStab, eStabTot, eSetTot, nbFree, eEltRed, eStabMatr, ListMatrStabGens, iRank, preEXTsumDirect, ListPlanes, ePlane, EXTface, eFacIneq, eVertRed, eVertOpp, ListEquaFace, rnk, DoPolyhedralCheck, GetListBelt, FuncInsertVertex, ListReprCoset, O, ListReprElement, eNewVert, lenDoubl, TheIncident, NSP, ListPlus, ListMinus, ListOrbitInfo, iDoubl, TheOption, LFC, DoCheckVoronoi, iFaceEXT, nbFaceEXT, TestFacetDefinition, eRecOrbit, testFacet, GetIntersectionPolytope, GetDefinedLinearSpann, iOrbitFacet, nbOrbitFacet, TheLinSpann, rnkLin, rnkFace, GetVertexExpression, GetListVoronoi, AllFacetCentrallySymmetric, ListVertVoronoi, eStabCell, GetSumDirectMethod;
  eMatrixGRP:=DataLattice.MatrixGRP;
  n:=DataLattice.n;
  ListFreeVect:=FreeInformations.ListFreeVect;
  nbFree:=Length(ListFreeVect);
  ListFreeVectTot:=Concatenation(ListFreeVect, -ListFreeVect);
  FuncGetPermutation:=function(eMat)
    local eList;
    eList:=List(ListFreeVect, x->GetPositionAntipodal(ListFreeVect, x*eMat));
    return PermList(eList);
  end;
  ListPermGens:=[];
  ListPermGensTot:=[];
  ListMatrGens:=GeneratorsOfGroup(eMatrixGRP);
  for eBigGen in ListMatrGens
  do
    eGen:=FuncExplodeBigMatrix(eBigGen).MatrixTransformation;
    ePerm:=FuncGetPermutation(eGen);
    ePermTot:=PermList(List(ListFreeVectTot, x->Position(ListFreeVectTot, x*eGen)));
    Add(ListPermGens, ePerm);
    Add(ListPermGensTot, ePermTot);
  od;
  PermGRPfree:=Group(ListPermGens);
  PermGRPfreeTot:=Group(ListPermGensTot);
  phi:=GroupHomomorphismByImagesNC(eMatrixGRP, PermGRPfree, ListMatrGens, ListPermGens);
  phiTot:=GroupHomomorphismByImagesNC(eMatrixGRP, PermGRPfreeTot, ListMatrGens, ListPermGensTot);
  eSetTot:=Concatenation(eSetInput, List(eSetInput, x->x+nbFree));
  eStabTot:=Stabilizer(PermGRPfreeTot, eSetTot, OnSets);
  eStab:=Stabilizer(PermGRPfree, eSetInput, OnSets);
  TheOption:=1;
  if TheOption=1 then
    eStabMatr:=PreImage(phi, eStab);
  elif TheOption=2 then
    eStabMatr:=Group([IdentityMat(n+1)]);
  else
    Error("Please put your choice here");
  fi;
  #
  EXTcomplete:=[];
  EXTdesc:=[];
  ListOrbitClusterFacet:=[];
  ListOrbitInfo:=[];
  AllFacetCentrallySymmetric:=true;
  FuncInsertVertex:=function(eNewVert)
    local pos, eHelpComp;
    pos:=Position(EXTcomplete, eNewVert);
    if pos=fail then
      O:=Orbit(eStabMatr, eNewVert);
      Print("        |O|=", Length(O), "\n");
      Append(EXTcomplete, ShallowCopy(O));
      Append(EXTdesc, ListWithIdenticalEntries(Length(O), eNewVert));
    fi;
  end;
  GetIntersectionPolytope:=function(eRecOrbit)
    local EXTfaceRed, eOrigin, ListVect1, ListVect2, ListVectTot, eTotBasis, ListIneqProj, eVectRelevant, eNorm, eIneq, eIneqProj, eSolution, eTotSpann;
    EXTfaceRed:=RowReduction(eRecOrbit.EXTface).EXT;
    eOrigin:=EXTfaceRed[1];
    ListVect1:=List([2..Length(EXTfaceRed)], x->EXTfaceRed[x]-eOrigin);
    if Length(eRecOrbit.ListVectZonAdd) > 0 then
      ListVect2:=RowReduction(eRecOrbit.ListVectZonAdd).EXT;
    else
      ListVect2:=[];
    fi;
    ListVectTot:=Concatenation(ListVect1, ListVect2);
    if RankMat(ListVectTot)<>n-1 then
      Error("We have a clear RankInconsistency");
    fi;
    eTotSpann:=Concatenation([eOrigin], ListVectTot);
    eTotBasis:=RowReduction(eTotSpann).EXT;
    ListIneqProj:=[];
    for eVectRelevant in ListRelevantVector
    do
      eNorm:=eVectRelevant*DataLattice.GramMat*eVectRelevant;
      eIneq:=Concatenation([eNorm], -2*DataLattice.GramMat*eVectRelevant);
      eIneqProj:=eTotBasis*eIneq;
      Add(ListIneqProj, eIneqProj);
    od;
    return ListIneqProj;
  end;
  TestFacetDefinition:=function(eRecOrbit)
    local ListIneqProj, eSolution;
    ListIneqProj:=GetIntersectionPolytope(eRecOrbit);
    eSolution:=SearchPositiveRelationSimple(ListIneqProj);
    if eSolution<>false then
      return true;
    fi;
    return false;
  end;
  GetDefinedLinearSpann:=function(eRecOrbit)
    local ListIneqProj, TheSpannedSpace;
    ListIneqProj:=GetIntersectionPolytope(eRecOrbit);
    TheSpannedSpace:=LinearDeterminedByInequalities(ListIneqProj);
    if RankMat(TheSpannedSpace)> n+1 then
      Print("Please debug from that point\n");
      Print(NullMat(9));
    fi;
    return TheSpannedSpace;
  end;
  for iRank in [0..n-1]
  do
    nbOrbit:=Length(ListListStrongTrans[iRank+1]);
    Print("iRank=", iRank, "/", n, "\n");
    for iOrbit in [1..nbOrbit]
    do
      eOrbit:=ListListStrongTrans[iRank+1][iOrbit];
      eCent:=eOrbit.EXTiso;
      Print("  rnk=", RankMat(eOrbit.EXTvoronoiFace), "\n");
      eRecO:=OrbitWithAction(eMatrixGRP, eCent, OnPoints);
      O:=Orbits(eStabMatr, eRecO.ListCoset, OnPoints);
      ListReprCoset:=List(O, x->x[1]);
      ListReprElement:=List(ListReprCoset, x->eRecO.ListElement[Position(eRecO.ListCoset, x)]);;
      len:=Length(eRecO.ListElement);
      lenDoubl:=Length(ListReprElement);
      Print("  iOrbit=", iOrbit, "/", nbOrbit, " |O|=", len, " |Odoubl|=", lenDoubl, "\n");
      for iDoubl in [1..lenDoubl]
      do
        Print("    iDoubl=", iDoubl, "/", lenDoubl, "\n");
        eElt:=ListReprElement[iDoubl];
        eEltRed:=FuncExplodeBigMatrix(eElt).MatrixTransformation;
        eStabCell:=Stabilizer(eStabMatr, ListReprCoset[iDoubl], OnPoints);
        eEltImg1:=FuncGetPermutation(eEltRed);
        eEltImg2:=PermList(List(ListFreeVectTot, x->Position(ListFreeVectTot, x*eEltRed)));
        EXTface:=eOrbit.EXTvoronoiFace*eElt;
        ListVectorTrans:=[];
        eVectTransSum:=ListWithIdenticalEntries(n+1,0);
        for iPos in eOrbit.ListFoundPos
        do
          eImg1:=OnPoints(iPos, eEltImg1);
          if eImg1 in eSetInput then
            eImg2:=OnPoints(iPos, eEltImg2);
            eVectTrans:=ListFreeVectTot[eImg2];
            Add(ListVectorTrans, eVectTrans);
            eVectTransSum:=eVectTransSum+Concatenation([0],eVectTrans);
          fi;
        od;
        for iPos in eOrbit.ListFoundNeg
        do
          eImg1:=OnPoints(iPos, eEltImg1);
          if eImg1 in eSetInput then
            eImg2:=OnPoints(iPos, eEltImg2);
            eVectTrans:=-ListFreeVectTot[eImg2];
            Add(ListVectorTrans, eVectTrans);
            eVectTransSum:=eVectTransSum+Concatenation([0],eVectTrans);
          fi;
        od;
        ListVectZon:=[];
        ListVectZonAdd:=[];
        for iPos in eOrbit.ListStrongTrans
        do
          eImg1:=OnPoints(iPos, eEltImg1);
          if eImg1 in eSetInput then
            eVect:=ListFreeVect[eImg1];
            eVectExt:=Concatenation([0], eVect);
            if SolutionMat(EXTface, eVectExt)<>fail then
              Error("Inconsistency for strongly transversal vector");
            fi;
            Add(ListVectZon, eVect);
            Add(ListVectZonAdd, eVectExt);
          fi;
        od;
        for iPos in eOrbit.ListFoundZero
        do
          eImg1:=OnPoints(iPos, eEltImg1);
          if eImg1 in eSetInput then
            eVect:=ListFreeVect[eImg1];
            eVectExt:=Concatenation([0], eVect);
            if SolutionMat(EXTface, eVectExt)=fail then
              Error("Inconsistency for parallel vector");
            fi;
            Add(ListVectZon, eVect);
            Add(ListVectZonAdd, eVectExt);
          fi;
        od;
        EXTtot:=Concatenation(EXTface, ListVectZonAdd);
        if RankMat(EXTtot)=n+1 then
          Add(ListOrbitClusterFacet, rec(iDoubl:=iDoubl, iRank:=iRank, iOrbit:=iOrbit, eElt:=eElt));
        fi;
        rnk:=RankMat(EXTtot);
        if rnk=n then
          ListEXT:=[];
          for eVect in ListVectZonAdd
          do
            Add(ListEXT, [eVect, -eVect]);
          od;
          Print("    iRank=", iRank, " iDoubl=", iDoubl, "/", lenDoubl, " |ListVectZon|=", Length(ListVectZonAdd), " |EXT|=", Length(EXTface), "\n");
          Add(ListEXT, EXTface);
          preEXTsum:=MINKSum_Generic(ListEXT, eStabCell);
          EXTsum:=List(preEXTsum, x->x+eVectTransSum);
          Print("      |EXTsum|=", Length(EXTsum), " rnk=", RankMat(EXTsum), " |EXTcomplete|=", Length(EXTcomplete), "\n");
          ListEquaFace:=NullspaceMat(TransposedMat(EXTsum));
          if Length(ListEquaFace)<>1 then
            Error("We have an inconsistency");
          fi;
          eFacIneq:=ListEquaFace[1];
          eVertRed:=EXTface[1]{[2..n+1]};
          eVertOpp:=Concatenation([1], -eVertRed);
          if eFacIneq*eVertOpp < 0 then
            eFacIneq:=-eFacIneq;
          fi;
          eRecOrbit:=rec(iRank:=iRank,
                         iOrbit:=iOrbit,
                         iDoubl:=iDoubl,
                         EXTsum:=EXTsum,
                         eElt:=eElt,
                         EXTface:=EXTface,
                         ListEXT:=ListEXT,
                         eFacIneq:=eFacIneq,
                         eStabCell:=eStabCell,
                         preEXTsum:=preEXTsum,
                         ListVectorTrans:=ListVectorTrans,
                         eVectTransSum:=eVectTransSum,
                         ListVectZonAdd:=ListVectZonAdd);
          testFacet:=TestFacetDefinition(eRecOrbit);
          Print("      testFacet=", testFacet, "\n");
          if testFacet=true then
            TheLinSpann:=GetDefinedLinearSpann(eRecOrbit);
            rnkLin:=RankMat(TheLinSpann);
            rnkFace:=RankMat(EXTface);
            Print("      rnkLin=", rnkLin, " rnkFace=", RankMat(EXTface), "\n");
            if rnkLin=rnkFace then
              Add(ListOrbitInfo, eRecOrbit);
              if IsCentrallySymmetric(EXTsum)=false then
                AllFacetCentrallySymmetric:=false;
              fi;
              for eNewVert in EXTsum
              do
                FuncInsertVertex(eNewVert);
              od;
            fi;
          fi;
        fi;
      od;
    od;
  od;
  Print("|EXTcomplete|=", Length(EXTcomplete), "\n");
  if IsCentrallySymmetric(EXTcomplete)=false then
    Error("Failure of central symmetry of the sum, PANIC!");
  fi;
  ListPermGensEXT:=[];
  ListMatrStabGens:=GeneratorsOfGroup(eStabMatr);
  for eGen in ListMatrStabGens
  do
    eList:=List(EXTcomplete, x->Position(EXTcomplete, x*eGen));
    ePerm:=PermList(eList);
    Add(ListPermGensEXT, ePerm);
  od;
  GetListBelt:=function()
    local ListListOrbitSubset, eSet, EXTface, TheStab, TheStabRed, ListOrbitSubset;
    ListListOrbitSubset:=[];
    for eSet in ListOrbitFacetsInc
    do
      EXTface:=EXTcomplete{eSet};
      TheStab:=Stabilizer(PermGRPext, eSet, OnSets);
      TheStabRed:=SecondReduceGroupAction(TheStab, eSet);
      ListOrbitSubset:=DualDescriptionStandard(EXTface, TheStabRed);
      Add(ListListOrbitSubset, ListOrbitSubset);
    od;
    return KernelBeltComputation(EXTcomplete, PermGRPext, ListOrbitFacetsInc, ListListOrbitSubset);
  end;
  GetVertexExpression:=function(eAskVert)
    local ListLen, nbVect, TheProd, eListPos, ListFoundSymbol, eSumVert, i, eVect, eVectExt;
    nbVect:=Length(eSetInput);
    ListLen:=ListWithIdenticalEntries(nbVect, 2);
    Add(ListLen, Length(ListVertVoronoi));
    TheProd:=2^(nbVect) * Length(ListVertVoronoi);
    eListPos:=InitialDirectProduct(ListLen);
    ListFoundSymbol:=[];
    while(true)
    do
      eSumVert:=ListWithIdenticalEntries(n+1,0);
      for i in [1..nbVect]
      do
        eVect:=ListFreeVect[eSetInput[i]];
        eVectExt:=Concatenation([0], eVect);
        if eListPos[i]=1 then
          eSumVert:=eSumVert + eVectExt;
        else
          eSumVert:=eSumVert - eVectExt;
        fi;
      od;
      eSumVert:=eSumVert + ListVertVoronoi[eListPos[nbVect+1]];
      if eSumVert=eAskVert then
        Add(ListFoundSymbol, eListPos);
      fi;
      eListPos:=NextDirectProduct(ListLen, eListPos);
      if eListPos=false then
        break;
      fi;
    od;
    return ListFoundSymbol;
  end;
  PermGRPext:=Group(ListPermGensEXT);
  ListOrbitFacetsInc:=[];
  ListPlanes:=[];
  nbOrbitFacet:=Length(ListOrbitInfo);
  for iOrbitFacet in [1..nbOrbitFacet]
  do
    Print("iOrbitFacet=", iOrbitFacet, "/", nbOrbitFacet, "\n");
    eFaceEXT:=ListOrbitInfo[iOrbitFacet].EXTsum;
    eSetFace:=Set(List(eFaceEXT, x->Position(EXTcomplete, x)));
    NSP:=NullspaceMat(TransposedMat(eFaceEXT));
    if Length(NSP)<>1 then
      Error("Rank is not correct");
    fi;
    ePlane:=RemoveFraction(NSP[1]);
    TheIncident:=Filtered([1..Length(EXTcomplete)], x->EXTcomplete[x]*ePlane=0);
    ListPlus:=Filtered([1..Length(EXTcomplete)], x->EXTcomplete[x]*ePlane>0);
    ListMinus:=Filtered([1..Length(EXTcomplete)], x->EXTcomplete[x]*ePlane<0);
    if TheIncident<>eSetFace then
      Error("We find new vertices!!!!");
    fi;
    if Length(ListPlus)>0 and Length(ListMinus)>0 then
      Error("The set does not define a facet");
    fi;
    Add(ListOrbitFacetsInc, eSetFace);
    Add(ListPlanes, ePlane);
  od;
  return rec(EXTcomplete:=EXTcomplete,
             AllFacetCentrallySymmetric:=AllFacetCentrallySymmetric,
             PermGRPext:=PermGRPext,
             GetListBelt:=GetListBelt,
             ListOrbitClusterFacet:=ListOrbitClusterFacet,
             ListOrbitInfo:=ListOrbitInfo,
             ListPlanes:=ListPlanes,
             ListOrbitFacetsInc:=ListOrbitFacetsInc);
end;


FreedomStructure_Enumerate4configuration:=function(DataLattice, ListEXTvoronoiFace, ListListStrongTrans, ListFreeVectors)
  local n, eSolutionFirst, nbFace, ListLen, ListSolution, NewListSolution, IsDone, eSetInt, ePosBegin, TheRNK, eVal, eNewVal, eNewSet, TheNewRNK, eNewSolution, iFaceSelect, eSolution, iFace, Rmat, RmatNew, TotSpace, eList, NewRNK, TotalListSolution, TheDiff, TheMax, ListForbidden, FuncFindMinimalSubsets;
  n:=DataLattice.n;
  eSolutionFirst:=[];
  nbFace:=Length(ListEXTvoronoiFace);
  ListLen:=List(ListListStrongTrans, Length);
  TotSpace:=[];
  for eList in ListListStrongTrans
  do
    TotSpace:=Union(TotSpace, eList);
  od;
  Print("nbFace=", nbFace, " ListLen=", ListLen, " ListRank=", List(ListEXTvoronoiFace, RankMat), "\n");
  TotalListSolution:=[eSolutionFirst];
  for iFace in [1..nbFace]
  do
    Print("iFace=", iFace, "\n");
    ListSolution:=ShallowCopy(TotalListSolution);
    TotalListSolution:=[];
    while(true)
    do
      NewListSolution:=[];
      Print("|ListSolution|=", Length(ListSolution), "\n");
      for eSolution in ListSolution
      do
        if Length(eSolution)=0 then
          TheMax:=0;
        else
          TheMax:=Maximum(eSolution);
        fi;
        TheDiff:=Filtered(ListListStrongTrans[iFace], x->x>TheMax);
        eSetInt:=Intersection(ListListStrongTrans[iFace], eSolution);
        Rmat:=Concatenation(ListEXTvoronoiFace[iFace], List(eSetInt, x->Concatenation([0], ListFreeVectors[x])));
        TheRNK:=RankMat(Rmat);
        if TheRNK < n then
          for eVal in TheDiff
          do
            eNewSolution:=Union(eSolution, [eVal]);
            eNewSet:=Union(eSetInt, [eVal]);
            Rmat:=Concatenation(ListEXTvoronoiFace[iFace], List(eNewSet, x->Concatenation([0], ListFreeVectors[x])));
            NewRNK:=RankMat(Rmat);
            if NewRNK > TheRNK then
              Add(NewListSolution, eNewSolution);
            fi;
          od;
        else
          Add(TotalListSolution, eSolution);
        fi;
      od;
      if Length(NewListSolution)=0 then
        break;
      fi;
      ListSolution:=ShallowCopy(NewListSolution);
    od;
  od;
  Print("FS_Enumerate4configuration, |TotalListSolution|=", Length(TotalListSolution), "\n");
  ListForbidden:=[];
  FuncFindMinimalSubsets:=function(eSolution)
    local GetListRank, ListRemove, FinalListRemove, ListRankCan, len, NewListRemove, eDiff, WeFindOne, i, eNewRemove, eNewSolution, eNewListRank, IsOK, iFace, MaxDiff;
    GetListRank:=function(eSolution)
      local ListRank, iFace, eSetInt, Rmat, TheRNK;
      ListRank:=[];
      for iFace in [1..nbFace]
      do
        eSetInt:=Intersection(ListListStrongTrans[iFace], eSolution);
        Rmat:=Concatenation(ListEXTvoronoiFace[iFace], List(eSetInt, x->Concatenation([0], ListFreeVectors[x])));
        TheRNK:=RankMat(Rmat);
        Add(ListRank, TheRNK);
      od;
      return ListRank;
    end;
    ListRemove:=[ [] ];
    FinalListRemove:=[];
    ListRankCan:=GetListRank(eSolution);
    len:=Length(eSolution);
    while(true)
    do
      NewListRemove:=[];
      for eDiff in ListRemove
      do
        if Length(eDiff)=0 then
          MaxDiff:=0;
        else
          MaxDiff:=Maximum(eDiff);
        fi;
        WeFindOne:=false;
        for i in [MaxDiff+1..len]
        do
          eNewRemove:=Union(eDiff, [i]);
          eNewSolution:=Difference(eSolution, eSolution{eNewRemove});
          eNewListRank:=GetListRank(eNewSolution);
          IsOK:=true;
          for iFace in [1..nbFace]
          do
            if eNewListRank[iFace]<ListRankCan[iFace] then
              IsOK:=false;
            fi;
          od;
          if IsOK=true then
            WeFindOne:=true;
            Add(NewListRemove, eNewRemove);
          fi;
        od;
        if WeFindOne=false then
          Add(FinalListRemove, eDiff);
        fi;
      od;
      if Length(NewListRemove)=0 then
        break;
      fi;
      ListRemove:=ShallowCopy(NewListRemove);
    od;
    return Set(List(FinalListRemove, x->Difference(eSolution, eSolution{x})));
  end;
  for eSolution in TotalListSolution
  do
    ListForbidden:=Union(ListForbidden, FuncFindMinimalSubsets(eSolution));
  od;
  Print("FS_Enumerate4configuration, |ListForbidden|=", Length(ListForbidden), "\n");
  Print("FS_Enumerate4configuration, sizes : ", Collected(List(ListForbidden, Length)), "\n");
  return ListForbidden;
end;


FreedomStructure_EnumerateRank2substructures:=function(ListCenters, GRPpermCenters)
  local nbCenter, ListOrbitsPossibleBelts, O1, eO1, FuncInsert, eElt1, eElt1opp, eSet1, eStab, O2, eO2, eElt2, eMat, eSet, Ocenter;
  Print("|GRPpermCenters|=", Order(GRPpermCenters), "\n");
  Print("|ListCenters|=", Length(ListCenters), "\n");
  nbCenter:=Length(ListCenters);
  Ocenter:=Orbits(GRPpermCenters, [1..nbCenter], OnPoints);
  ListOrbitsPossibleBelts:=[];
  FuncInsert:=function(eSet)
    local fSet, test, eStab, Osize, iO;
    for fSet in ListOrbitsPossibleBelts
    do
      test:=RepresentativeAction(GRPpermCenters, eSet, fSet, OnSets);
      if test<>fail then
        return;
      fi;
    od;
    eStab:=Stabilizer(GRPpermCenters, eSet, OnSets);
    Osize:=Order(GRPpermCenters)/Order(eStab);
    Add(ListOrbitsPossibleBelts, eSet);
    Print("quasi4belt, i=", Length(ListOrbitsPossibleBelts), " |eStab|=", Order(eStab), " |O|=", Osize, " |eSet|=", Length(eSet));
    Print(" [");
    for iO in [1..Length(Ocenter)]
    do
      if iO > 1 then
        Print(",");
      fi;
      Print(Length(Intersection(Ocenter[iO], eSet)));
    od;
    Print("]\n");
  end;
  O1:=Orbits(GRPpermCenters, [1..nbCenter], OnPoints);
  for eO1 in O1
  do
    eElt1:=eO1[1];
    eElt1opp:=Position(ListCenters, -ListCenters[eElt1]);
    eSet1:=Set([eElt1, eElt1opp]);
    eStab:=Stabilizer(GRPpermCenters, eSet1, OnSets);
    O2:=Orbits(eStab, Difference([1..nbCenter], eSet1), OnPoints);
    for eO2 in O2
    do
      eElt2:=eO2[1];
      eMat:=[ListCenters[eElt1], ListCenters[eElt2]];
      eSet:=Filtered([1..nbCenter], x->SolutionMat(eMat, ListCenters[x])<>fail);
      FuncInsert(eSet);
    od;
  od;
  Print("|ListOrbitsPossibleBelts|=", Length(ListOrbitsPossibleBelts), "\n");
  return ListOrbitsPossibleBelts;
end;


FreedomStructure_OneEnumeration:=function(GRPperm)
  local ListCases, FuncInsert, DoAppend, GetAll;
  ListCases:=[];
  FuncInsert:=function(fSet)
    local eSet, eTest;
    for eSet in ListCases
    do
      eTest:=RepresentativeAction(GRPperm, eSet, fSet, OnSets);
      if eTest<>fail then
        return;
      fi;
    od;
    Add(ListCases, fSet);
  end;
  DoAppend:=function(ListSet)
    local eSet;
    for eSet in ListSet
    do
      FuncInsert(eSet);
    od;
  end;
  GetAll:=function()
    return ListCases;
  end;
  return rec(FuncInsert:=FuncInsert,
             DoAppend:=DoAppend,
             GetAll:=GetAll);
end;


FreedomStructure_GetForbiddenSubsetsFromFreeVectorStrongTransversal:=function(DataLattice, BeltFreeInformations, ListStronglyTransversalFaces)
  local n, GramMat, GRPpermFreeVect, ListForbiddenSubsets, ListCenterMod2, GRPanti, GRPpermCenters, ListListStrongTrans, ListFreeVect, ListEXTvoronoiFace, nbAnti, eSet, ListOrbitQuasiBelt, eOrb, NewListGens, eGen, nbElt, eList, eOrbit, iOrbit, OrbInfo, FreeInformations, ListPermElt, eCentRed, eDen, iDim, len, TheListOrbit, ListBigMat, ListGeneration_Case1, MainEnum_Case1, ListGeneration_Case2, MainEnum_Case2, ListGeneration_Case3, MainEnum_Case3, MainEnum, ListGeneration1, ListGeneration2, ListGeneration3, iOrb, eOrbSelectAnti, ListReprAnti, eListAnti, GRPpermAnti;
  n:=DataLattice.n;
  GramMat:=DataLattice.GramMat;
  FreeInformations:=BeltFreeInformations.FuncGetAllFreeVectors();
  GRPpermFreeVect:=FreeInformations.PermGRPfree;
  ListFreeVect:=FreeInformations.ListFreeVect;
  MainEnum:=FreedomStructure_OneEnumeration(GRPpermFreeVect);
  MainEnum_Case1:=FreedomStructure_OneEnumeration(GRPpermFreeVect);
  MainEnum_Case2:=FreedomStructure_OneEnumeration(GRPpermFreeVect);
  MainEnum_Case3:=FreedomStructure_OneEnumeration(GRPpermFreeVect);
  len:=Length(ListStronglyTransversalFaces);
  ListCenterMod2:=[];
  ListEXTvoronoiFace:=[];
  ListListStrongTrans:=[];
  for iDim in [0..len-1]
  do
    TheListOrbit:=ListStronglyTransversalFaces[iDim+1];
    for iOrbit in [1..Length(TheListOrbit)]
    do
      eOrbit:=TheListOrbit[iOrbit];
      eDen:=RemoveFractionPlusCoef(eOrbit.EXTiso).TheMult;
      if eDen=2 and eOrbit.testCent=false then
        Error("We have an inconsistency in central symmetry");
      fi;
      Print("eDen=", eDen, " rnk=", eOrbit.rnk, " testCent=", eOrbit.testCent, "\n");
      if eOrbit.testCent=false then
        if eOrbit.rnk > n-1 then
          Print("call 1 elimination\n");
          ListGeneration1:=FreedomStructure_GetFixedSubrank(eOrbit.EXTvoronoiFace, eOrbit.ListStrongTrans, ListFreeVect, GRPpermFreeVect, n-1);
          MainEnum.DoAppend(ListGeneration1);
          MainEnum_Case1.DoAppend(ListGeneration1);
        fi;
      fi;
      if eOrbit.testCent=true then
        if eOrbit.rnk > n then
          Print("call 2 elimination\n");
          ListGeneration2:=FreedomStructure_GetFixedSubrank(eOrbit.EXTvoronoiFace, eOrbit.ListStrongTrans, ListFreeVect, GRPpermFreeVect, n);
          MainEnum.DoAppend(ListGeneration2);
          MainEnum_Case2.DoAppend(ListGeneration2);
        fi;
        if eOrbit.rnk > n-1 then
          eCentRed:=eOrbit.EXTiso{[2..n+1]};
          OrbInfo:=OrbitWithAction(DataLattice.PointGRP, eCentRed, OnPoints);
          Print("Appending to ListCentersMod2, siz=", Length(OrbInfo.ListCoset), "\n");
          Append(ListCenterMod2, OrbInfo.ListCoset);
          ListBigMat:=List(OrbInfo.ListElement, x->FuncCreateBigMatrix(ListWithIdenticalEntries(n, 0), x));
          ListPermElt:=List(OrbInfo.ListElement, FreeInformations.FuncGetPermutation);
          Append(ListListStrongTrans, List(ListPermElt, x->OnSets(eOrbit.ListStrongTrans, x)));
          Append(ListEXTvoronoiFace, List(ListBigMat, x->eOrbit.EXTvoronoiFace*x));
        fi;
      fi;
    od;
  od;
  NewListGens:=[];
  for eGen in GeneratorsOfGroup(DataLattice.PointGRP)
  do
    eList:=List(ListCenterMod2, x->Position(ListCenterMod2, x*eGen));
    Add(NewListGens, PermList(eList));
  od;
  GRPpermCenters:=Group(NewListGens);
  GRPanti:=Group([-IdentityMat(n)]);
  eListAnti:=List(ListCenterMod2, x->Position(ListCenterMod2, -x));
  GRPpermAnti:=Group([PermList(eListAnti)]);
  ListReprAnti:=Set(List(Orbits(GRPpermAnti, [1..Length(ListCenterMod2)], OnPoints), x->x[1]));
  ListOrbitQuasiBelt:=FreedomStructure_EnumerateRank2substructures(ListCenterMod2, GRPpermCenters);
  for iOrb in [1..Length(ListOrbitQuasiBelt)]
  do
    eOrb:=ListOrbitQuasiBelt[iOrb];
    eOrbSelectAnti:=Intersection(eOrb, ListReprAnti);
    nbAnti:=Length(eOrbSelectAnti);
    Print("iOrb=", iOrb, " nbAnti=", nbAnti, "\n");
    if nbAnti > 3 then
      for eSet in Combinations(eOrbSelectAnti, 4)
      do
        ListGeneration3:=FreedomStructure_Enumerate4configuration(DataLattice, ListEXTvoronoiFace{eSet}, ListListStrongTrans{eSet}, ListFreeVect);
        Print("|ListGeneration3|=", Length(ListGeneration3), "\n");
        MainEnum.DoAppend(ListGeneration3);
        MainEnum_Case3.DoAppend(ListGeneration3);
      od;
    fi;
  od;
  ListForbiddenSubsets:=MainEnum.GetAll();
  ListGeneration_Case1:=MainEnum_Case1.GetAll();
  ListGeneration_Case2:=MainEnum_Case2.GetAll();
  ListGeneration_Case3:=MainEnum_Case3.GetAll();
  Print("|ListForbiddenSubsets|=", Length(ListForbiddenSubsets), "\n");
  Print("|ListGeneration_Case1|=", Length(ListGeneration_Case1), "\n");
  Print("|ListGeneration_Case2|=", Length(ListGeneration_Case2), "\n");
  Print("|ListGeneration_Case3|=", Length(ListGeneration_Case3), "\n");
  return rec(ListGeneration:=ListForbiddenSubsets,
             ListGeneration_Case1:=ListGeneration_Case1,
             ListGeneration_Case2:=ListGeneration_Case2,
             ListGeneration_Case3:=ListGeneration_Case3);
end;





SingleListOrbit:=function(TheEXT, eSet, AddiInfo)
  local RNK, FAC, O, RelFAC, eRep, ListVertStatus, ListOrbit, FuncReturnPosition, iOrb, ListSel, VertSet, RelVertSet, eVert, FACinc;
  O:=Orbits(AddiInfo.Stab, Difference([1..Length(TheEXT)], eSet), OnPoints);
  RelFAC:=[];
  # it seems that we cannot avoid generating all facets
  for eRep in AddiInfo.ListOrbitRelFacet
  do
    Append(RelFAC, Orbit(AddiInfo.Stab, eRep, OnSets));
  od;
  FAC:=List(RelFAC, x->FindFacetInequality(TheEXT, x));
  RNK:=RankMat(FAC);
  FuncReturnPosition:=function(eVert)
    local iO;
    for iO in [1..Length(O)]
    do
      if Position(O[iO], eVert)<>fail then
        return iO;
      fi;
    od;
  end;
  ListVertStatus:=ListWithIdenticalEntries(Length(O), 1);
  ListOrbit:=[];
  for iOrb in [1..Length(O)]
  do
    if ListVertStatus[iOrb]=1 then
      ListSel:=Filtered([1..Length(RelFAC)], x->O[iOrb][1] in RelFAC[x]);
      FACinc:=FAC{ListSel};
      ListVertStatus[iOrb]:=0;
      if Length(ListSel)>0 and RankMat(FACinc)=RNK-1 then
        VertSet:=Intersection(RelFAC{ListSel});
        RelVertSet:=Difference(VertSet, eSet);
        for eVert in RelVertSet
        do
          ListVertStatus[FuncReturnPosition(eVert)]:=0;
        od;
        Add(ListOrbit, Union(VertSet, eSet));
      fi;
    fi;
  od;
  return ListOrbit;
end;


#
# return the list of orbits of faces containing EXT
# with respect to the stabilizer of EXT.
ListOrbitContainingEXT:=function(DataLattice, DelaunayDatabase, TheSymbol, SoftComp)
  local EXT, StabEXT, TheLevel, ListOrbitExtensionsEXT, FuncInsert, iRecord, eRecord, eAddiInfo, TheEXT, ListOrbGenerated, eOrb, DelVal, FuncInvariantOfPair;
  # two solutions for isomorphy determination:
  # use local combinatorics of the Delaunay
  # or use the lattice functions for that (what we choosed)
  # This is a tradeoff
  FuncInvariantOfPair:=function(EXT, EXTover)
    # at present this code works only for lattices
    # due to the number theoretic invariants used.
    local TheInvOver, ListIsoCenter, DelVal, eIso;
    TheInvOver:=DelaunayInvariantLattice(rec(GramMat:=DataLattice.GramMat), EXTover);
    ListIsoCenter:=[];
    for DelVal in [3,5,7,11]
    do
      eIso:=(Isobarycenter(EXTover)+DelVal*Isobarycenter(EXT))/(DelVal+1);
      Add(ListIsoCenter, ListFactors(eIso));
    od;
    return rec(TheInvOver:=TheInvOver, ListIsoCenter:=ListIsoCenter);
  end;
  EXT:=TheSymbol.EXT;
  StabEXT:=TheSymbol.StabEXT;
  TheLevel:=TheSymbol.TheLevel;
  ListOrbitExtensionsEXT:=[];
  DelVal:=1;
  FuncInsert:=function(eRecord1)
    local TheEXT1, EXT1, eIso1, EXT2, eIso2, StabEXT1, DStabEXT1, eSymbol1, eSymbol2, eInvariant;
    TheEXT1:=DelaunayDatabase.FuncDelaunayGetEXT(eRecord1.iOrb);
    EXT1:=TheEXT1{eRecord1.eSet}*eRecord1.eMat;
    eInvariant:=FuncInvariantOfPair(EXT, EXT1);
    eIso1:=(Isobarycenter(EXT1)+DelVal*Isobarycenter(EXT))/(DelVal+1);
    for eSymbol2 in ListOrbitExtensionsEXT
    do
      EXT2:=eSymbol2.EXT;
      eIso2:=(Isobarycenter(EXT2)+DelVal*Isobarycenter(EXT))/(DelVal+1);
      if eInvariant=eSymbol2.eInvariant then
        if DataLattice.FuncEquiv(EXT, EXT, eIso1, eIso2)<>false then
          return;
        fi;
      fi;
    od;
    DStabEXT1:=DataLattice.FuncAutom(EXT1, eIso1);
    StabEXT1:=DataLattice.FuncAutom(EXT1, Isobarycenter(EXT1));
    eSymbol1:=rec(EXT:=EXT1, StabEXT:=StabEXT1, DStabEXT:=DStabEXT1, TheLevel:=TheLevel+1, TheDel:=eRecord1, eInvariant:=eInvariant);
    Add(ListOrbitExtensionsEXT, eSymbol1);
  end;
  for iRecord in [1..Length(SoftComp.ListRecord)]
  do
    eRecord:=SoftComp.ListRecord[iRecord];
    eAddiInfo:=SoftComp.ListAdditionalInfo[iRecord];
    TheEXT:=DelaunayDatabase.FuncDelaunayGetEXT(eRecord.iOrb);
    ListOrbGenerated:=SingleListOrbit(TheEXT, eRecord.eSet, eAddiInfo);
    for eOrb in ListOrbGenerated
    do
      FuncInsert(rec(iOrb:=eRecord.iOrb, eMat:=eRecord.eMat, eSet:=eOrb));
    od;
  od;
  return ListOrbitExtensionsEXT;
end;

#
# using a random walk is probably the best here.
InitialPair:=function(DataLattice, DelaunayDatabase, TheVert)
  local n, TheMat, iOrb, TheEXT, TheEXTimg, iVert, eDiff, eMat;
  n:=DataLattice.n;
  TheMat:=IdentityMat(n+1);
  while(true)
  do
    for iOrb in [1..DelaunayDatabase.FuncDelaunayGetNumber()]
    do
      TheEXT:=DelaunayDatabase.FuncDelaunayGetEXT(iOrb);
      TheMat:=TheMat*Random(GeneratorsOfGroup(DataLattice.MatrixGRP));
      TheEXTimg:=TheEXT*TheMat;
      for iVert in [1..Length(TheEXT)]
      do
        eDiff:=TheVert-TheEXTimg[iVert];
        if IsIntegralVector(eDiff)=true then
          eMat:=FuncCreateBigMatrix(eDiff{[2..n+1]}, IdentityMat(n));
          return rec(EXT:=[TheVert],
                     StabEXT:=DataLattice.FuncAutom([TheVert], TheVert),
                     TheDel:=rec(iOrb:=iOrb, eMat:=TheMat*eMat, eSet:=[iVert]),
                     TheLevel:=0);
        fi;
      od;
    od;
  od;
end;




QuantizationIntegral:=function(DataLattice, DelaunayDatabase, TheVert)
  local n, GroupExpressionInTheBasis, FuncRespawn, TransformIntegral, FuncLiftIntegralStd, TheVol, TheBarycenter, TheRes, __RecursiveIntegralEvaluation, ListOrbitIntegrals, FuncCheckInBank, TheInit, TheInt, SecMoment, i, j;
  n:=DataLattice.n;
  #
  # find the barycenter of the orbit of TheExt under TheMatGrp
  # without computing the orbit.
  FuncRespawn:=function(OrdGrp, NBV, TheLevel)
    if NBV < 20 then
      return false;
    fi;
    if NBV > 130 then
      return true;
    fi;
    if OrdGrp > 10000 then
      return true;
    fi;
    if NBV>100 and OrdGrp>1000 then
      return true;
    fi;
    if TheLevel=2 then
      return false;
    fi;
    if NBV < 70 then
      return false;
    fi;
    if NBV > 110 and OrdGrp > 100 and TheLevel < 2 then
      return true;
    fi;
    return false;
  end;
  TransformIntegral:=function(INT1, TheBasis1, TheBasis2)
    local P, eVect;
    P:=List(TheBasis1, x->SolutionMat(TheBasis2, x));
    return AbsInt(DeterminantMat(P))*TransposedMat(P)*INT1*P;
  end;
  ListOrbitIntegrals:=[];
  FuncCheckInBank:=function(SoftComp1)
    local eIso1, TheBasis1, eSoftComp2, EXT2, TheBasis2, eIso2, eEquiv, ImageTheBasis2;
    eIso1:=SoftComp1.TheBarycenter;
    TheBasis1:=SoftComp1.TheBasis;
    for eSoftComp2 in ListOrbitIntegrals
    do
      TheBasis2:=eSoftComp2.TheBasis;
      eIso2:=eSoftComp2.TheBarycenter;
      if eSoftComp2.eInvariant=SoftComp1.eInvariant then
        eEquiv:=DataLattice.FuncEquiv(eSoftComp2.EXT, SoftComp1.EXT, eIso2, eIso1);
        if eEquiv<>false then
          ImageTheBasis2:=TheBasis2*eEquiv;
          return TransformIntegral(eSoftComp2.TheIntegral, ImageTheBasis2, TheBasis1);
        fi;
      fi;
    od;
    return fail;
  end;
  FuncLiftIntegralStd:=function(TheInt)
    local i, j, nRel, TheIntReturn;
    nRel:=Length(TheInt);
    TheIntReturn:=NullMat(nRel+1, nRel+1);
    for i in [1..nRel]
    do
      for j in [1..nRel]
      do
        TheIntReturn[i+1][j+1]:=TheInt[i][j]/(nRel+2);
      od;
    od;
    for i in [1..nRel]
    do
      TheIntReturn[i+1][1]:=TheInt[i][1]/(nRel+1);
      TheIntReturn[1][i+1]:=TheInt[1][i]/(nRel+1);
    od;
    TheIntReturn[1][1]:=TheInt[1][1]/nRel;
    return TheIntReturn;
  end;
  GroupExpressionInTheBasis:=function(TheBasis, TheMatGrp)
    local NewListGens, eGen, eNewGen, eVect, eLine;
    NewListGens:=[];
    for eGen in GeneratorsOfGroup(TheMatGrp)
    do
      eNewGen:=[];
      for eVect in TheBasis
      do
        eLine:=SolutionMat(TheBasis, eVect*eGen);
        Add(eNewGen, eLine);
      od;
      Add(NewListGens, eNewGen);
    od;
    return Group(NewListGens);
  end;
  __RecursiveIntegralEvaluation:=function(TheSymbol)
    local EXT, StabEXT, SoftComp, testCheck, testRespawn, TheIntegral, ListOrbit, Ccenter, iOrb, eOrbRecord, eOrbComp, eOrbCompBasis, NewBasis, ListVertDelaunay, TheMult, TheIntegralOrb;
    EXT:=TheSymbol.EXT;
    StabEXT:=TheSymbol.StabEXT;
    SoftComp:=SoftComputation(DataLattice, DelaunayDatabase, EXT, StabEXT, TheSymbol.TheDel);
    Print("Level=", TheSymbol.TheLevel, "  |EXT|=", Length(EXT), "  |Stab|=", Size(StabEXT), "  |Dels|=", SoftComp.NumberIncident, "\n");
    testCheck:=FuncCheckInBank(SoftComp);
    if testCheck<>fail then
      Print("Retrieved from the bank\n");
      SoftComp.TheIntegral:=testCheck;
      return SoftComp;
    fi;
    testRespawn:=FuncRespawn(Size(StabEXT), SoftComp.NumberIncident, TheSymbol.TheLevel);
    if testRespawn=true then
      TheIntegral:=NullMat(Length(SoftComp.TheBasis), Length(SoftComp.TheBasis));
      ListOrbit:=ListOrbitContainingEXT(DataLattice, DelaunayDatabase, TheSymbol, SoftComp);
      Ccenter:=SoftComp.TheBarycenter;
      Print("Respawn with ", Length(ListOrbit), " orbits\n");
      for iOrb in [1..Length(ListOrbit)]
      do
        eOrbRecord:=ListOrbit[iOrb];
        TheMult:=Size(StabEXT)/Size(eOrbRecord.DStabEXT);
        Print("Treating O", iOrb, "/", Length(ListOrbit), " |O", iOrb, "|=", TheMult, "\n");
        eOrbComp:=__RecursiveIntegralEvaluation(eOrbRecord);
        eOrbCompBasis:=eOrbComp.TheBasis;
        NewBasis:=Concatenation([Ccenter, eOrbCompBasis[1]-Ccenter], eOrbCompBasis{[2..Length(eOrbCompBasis)]});
        TheIntegralOrb:=TransformIntegral(FuncLiftIntegralStd(eOrbComp.TheIntegral), NewBasis, SoftComp.TheBasis);
        TheIntegral:=TheIntegral+TheMult*OrbitBarycenterSymmetricMatrix(TheIntegralOrb, GroupExpressionInTheBasis(SoftComp.TheBasis, StabEXT));
        Print("Volume=", TheIntegral[1][1], "\n");
      od;
      Print("End of Respawned computation\n");
    else
      ListVertDelaunay:=VoronoiPolytopeListVertices(DataLattice, DelaunayDatabase, StabEXT, SoftComp);
      TheIntegral:=DirectIntegral(ListVertDelaunay, SoftComp.TheBasis);
    fi;
    SoftComp.TheIntegral:=TheIntegral;
    Add(ListOrbitIntegrals, SoftComp);
    return SoftComp;
  end;
  TheInit:=InitialPair(DataLattice, DelaunayDatabase, TheVert);
  TheRes:=__RecursiveIntegralEvaluation(TheInit);
  TheInt:=TransformIntegral(TheRes.TheIntegral, TheRes.TheBasis, IdentityMat(n+1));
  SecMoment:=0;
  for i in [1..n]
  do
    for j in [1..n]
    do
      SecMoment:=SecMoment+DataLattice.GramMat[i][j]*TheInt[i+1][j+1];
    od;
  od;
  TheVol:=TheInt[1][1];
  TheBarycenter:=TheInt[1]/TheVol;
  return rec(SecMoment:=SecMoment, TheVolume:=TheVol, TheBarycenter:=TheBarycenter);
end;



FuncDirectEnumerationFreeVector:=function(PermGRP, ListVectorRed, ListBelt)
  local n, NullSol, ListSolution, nbBelt, nbVect, ListTotalSolution, NewListSolution, FuncInsert, eSol, H, iBeltMin, idx, VectorIdx, VectorSet, NSP, MatchedVectors, iVect, eList, MatchedBelt, iBelt;
  n:=Length(ListVectorRed[1]);
  NullSol:=rec(MatchedBelt:=[], MatchedVectors:=[], BasisSpace:=IdentityMat(n));
  ListSolution:=[NullSol];
  nbBelt:=Length(ListBelt);
  nbVect:=Length(ListVectorRed);
  ListTotalSolution:=[];
  while(true)
  do
    NewListSolution:=[];
    FuncInsert:=function(NewSol)
      local eSol;
      for eSol in NewListSolution
      do
        if RepresentativeAction(PermGRP, eSol.MatchedVectors, NewSol.MatchedVectors, OnSets)<>fail then
          return;
        fi;
      od;
      Add(NewListSolution, NewSol);
    end;
    for eSol in ListSolution
    do
      H:=Difference([1..nbBelt], eSol.MatchedBelt);
      if Length(H)=0 then
        Add(ListTotalSolution, rec(MatchedVectors:=eSol.MatchedVectors, BasisSpace:=eSol.BasisSpace));
      else
        iBeltMin:=Minimum(H);
        for idx in ListBelt[iBeltMin]
        do
          VectorIdx:=Concatenation(eSol.MatchedVectors, [idx]);
          VectorSet:=ListVectorRed{VectorIdx};
          NSP:=NullspaceMat(TransposedMat(VectorSet));
          if Length(NSP)>0 then
            MatchedVectors:=[];
            for iVect in [1..nbVect]
            do
              eList:=List(NSP, x->x*ListVectorRed[iVect]);
              if eList*eList=0 then
                Add(MatchedVectors, iVect);
              fi;
            od;
            MatchedBelt:=[];
            for iBelt in [1..nbBelt]
            do
              if Length(Intersection(ListBelt[iBelt], MatchedVectors))>0 then
                Add(MatchedBelt, iBelt);
              fi;
            od;
            FuncInsert(rec(MatchedBelt:=MatchedBelt, MatchedVectors:=MatchedVectors, BasisSpace:=NSP));
          fi;
        od;
      fi;
    od;
    ListSolution:=List(NewListSolution, x->x);
    Print("|ListSolution|=", Length(ListSolution), "\n");
    if Length(ListSolution)=0 then
      break;
    fi;
  od;
  return ListTotalSolution;
end;



FreenessBeltListing:=function(DataLattice, DelaunayDatabase, TheVert, VoronoiFacetInequalities)
  local n, GetBeltOrbits, ListBeltOrbits, ListBelt, VectorPres, GetVectorAndRepresentation, ListFreeVectors, ListBeltData, FuncGetAllFreeVectors, TestVectorFreeness, TestVectorScalCondition, GetFreeVectors, HasFreeVector, HasBeltOrbit, HasFullBelt, ComputeFreeVector, GetBeltAndBeltData, GetBelt_Equivariant, FuncPrintBeltInformation, ComputeBeltOrbit, ComputeBeltAndBeltData, ComputeGarber_Gavrilyuk_Magazinov_Condition, RaiseLevel, GetInitial;

  n:=DataLattice.n;
  HasFreeVector:=false;
  HasBeltOrbit:=false;
  HasFullBelt:=false;
  RaiseLevel:=function(ListOrbit)
    local NewListOrbit, FuncInsert, eOrbit, SoftComp, ListOrb, eOrb, TheLevel;
    NewListOrbit:=[];
    TheLevel:=ListOrbit[1].TheLevel+1;
    FuncInsert:=function(eRecord)
      local TheEXT1, EXT1, eIso1, EXT2, eIso2, NewSymbol, eSymbol, TheStabEXT, DStabEXT;
      TheEXT1:=DelaunayDatabase.FuncDelaunayGetEXT(eRecord.iOrb);
      EXT1:=TheEXT1{eRecord.eSet}*eRecord.eMat;
      eIso1:=(Isobarycenter(EXT1)+TheVert)/2;
      for eSymbol in ListOrbit
      do
        EXT2:=eSymbol.EXT;
        eIso2:=(Isobarycenter(EXT2)+TheVert)/2;
        if DataLattice.FuncEquiv([TheVert], [TheVert], eIso1, eIso2)<>false then
          return;
        fi;
      od;
      DStabEXT:=DataLattice.FuncAutom([TheVert], eIso1);
      TheStabEXT:=DataLattice.FuncAutom(EXT1, Isobarycenter(EXT1));
      NewSymbol:=rec(EXT:=EXT1, DStabEXT:=DStabEXT, StabEXT:=TheStabEXT, TheDel:=eRecord, TheLevel:=TheLevel);
      Add(NewListOrbit, NewSymbol);
    end;
    for eOrbit in ListOrbit
    do
      SoftComp:=SoftComputation(DataLattice, DelaunayDatabase, eOrbit.EXT, eOrbit.StabEXT, eOrbit.TheDel);
      ListOrb:=ListOrbitContainingEXT(DataLattice, DelaunayDatabase, eOrbit, SoftComp);
      for eOrb in ListOrb
      do
        FuncInsert(eOrb.TheDel);
      od;
    od;
    return NewListOrbit;
  end;
  GetInitial:=function()
    local TheInit, SoftComp;
    TheInit:=InitialPair(DataLattice, DelaunayDatabase, TheVert);
    SoftComp:=SoftComputation(DataLattice, DelaunayDatabase, TheInit.EXT, TheInit.StabEXT, TheInit.TheDel);
    return ListOrbitContainingEXT(DataLattice, DelaunayDatabase, TheInit, SoftComp);
  end;
  ComputeBeltOrbit:=function()
    local ListOrbit1, ListOrbit2;
    if HasBeltOrbit=true then
      return;
    fi;
    HasBeltOrbit:=true;
    ListOrbit1:=GetInitial();
    ListOrbit2:=RaiseLevel(ListOrbit1);
    ListBeltOrbits:=rec(ListOrbit1:=ListOrbit1, ListOrbit2:=ListOrbit2);
  end;
  ComputeGarber_Gavrilyuk_Magazinov_Condition:=function()
    local ListOrbit1, ListOrbit2, ListOrbit3, ListEdges_3, ListEdges, eOrb, pos, EXTsel, eEdge, Oedge, nbVert, ListEdgeVect, eVect, nbEdge, TheKernel, ListSixBelt, SetSixBelt, eSpace, eSet, TheSpannA, TheSpannB, TheSpann, i, j, NSP, eSixBelt, eEdgeVect, eVert, fVert, ListVertices, ListContainedEdges, ListContainedEdges_3, eSign, RecO, ListEdgeRel, eElt, rnkSpann, EXTface, iEdge, len, ListEdgeReorg, rnkKernel, ListStatus, fEdge;
    ListOrbit1:=GetInitial();
    ListOrbit2:=RaiseLevel(ListOrbit1);
    ListOrbit3:=RaiseLevel(ListOrbit2);
    ListEdges_3:=[];
    ListEdges:=[];
    for eOrb in ListOrbit2
    do
      EXTface:=List(eOrb.EXT, x->x{[2..n+1]});
      pos:=Position(eOrb.EXT, TheVert);
      if pos=fail then
        Error("Wrong orbit, clearly");
      fi;
      EXTsel:=Filtered(EXTface, x->GetPositionAntipodal(VectorPres.ListVectRed, x)<>fail);
      eEdge:=Set(List(EXTsel, x->GetPositionAntipodal(VectorPres.ListVectRed, x)));
      Oedge:=Orbit(VectorPres.GRPperm, eEdge, OnSets);
      if Length(eOrb.EXT)=3 then
        Append(ListEdges_3, Oedge);
      fi;
      Append(ListEdges, Oedge);
    od;
    Print("|ListEdges|=", Length(ListEdges), " |ListEdges_3|=", Length(ListEdges_3), "\n");
    nbVert:=Length(VectorPres.ListVectRed);
    ListEdgeVect:=[];
    for eEdge in ListEdges_3
    do
      eVect:=ListWithIdenticalEntries(nbVert, 0);
      eVect[eEdge[1]]:=1;
      eVect[eEdge[2]]:=-1;
      Add(ListEdgeVect, eVect);
    od;
    nbEdge:=Length(ListEdgeVect);
    Print("nbEdge=", nbEdge, " nbVert=", nbVert, "\n");
    if nbEdge=0 then
      TheKernel:=[];
    else
      TheKernel:=NullspaceMat(ListEdgeVect);
    fi;
    ListSixBelt:=[];
    for i in [1..nbVert-1]
    do
      for j in [i+1..nbVert]
      do
        eSpace:=VectorPres.ListVectRed{[i,j]};
        NSP:=NullspaceMat(TransposedMat(eSpace));
        eSet:=Filtered([1..nbVert], x->First(NSP, y->VectorPres.ListVectRed[x]*y<>0)=fail);
        if Length(NSP)<>n-2 then
          Error("Please engage in debugging at that point");
        fi;
        if Length(eSet)<2 then
          Error("At least two vectors should be solution");
        fi;
#        Print("|NSP|=", Length(NSP), " |eSet|=", Length(eSet), "\n");
        if Length(eSet)=3 then
          Add(ListSixBelt, eSet);
        fi;
      od;
    od;
    SetSixBelt:=Set(ListSixBelt);
    TheSpannA:=[];
    for eSixBelt in SetSixBelt
    do
      eEdgeVect:=ListWithIdenticalEntries(nbEdge,0);
      for i in [1..3]
      do
        j:=NextIdx(3,i);
        eVert:=eSixBelt[i];
        fVert:=eSixBelt[j];
        if eVert < fVert then
          eEdge:=[eVert, fVert];
          eSign:=1;
        else
          eEdge:=[fVert, eVert];
          eSign:=-1;
        fi;
        pos:=Position(ListEdges, eEdge);
        eEdgeVect[pos]:=eEdgeVect[pos] + eSign;
      od;
      if eEdgeVect*ListEdgeVect<>ListWithIdenticalEntries(nbVert,0) then
        Error("Not a cycle A");
      fi;
      Add(TheSpannA, eEdgeVect);
    od;
    Print("|TheSpannA|=", Length(TheSpannA), "\n");
    #
    TheSpannB:=[];
    for eOrb in ListOrbit3
    do
      EXTface:=List(eOrb.EXT, x->x{[2..n+1]});
      pos:=Position(eOrb.EXT, TheVert);
      if pos=fail then
        Error("Wrong orbit, clearly 2");
      fi;
      EXTsel:=Filtered(EXTface, x->GetPositionAntipodal(VectorPres.ListVectRed, x)<>fail);
      ListVertices:=Set(List(EXTsel, x->GetPositionAntipodal(VectorPres.ListVectRed, x)));
      ListContainedEdges:=Filtered(ListEdges, x->IsSubset(ListVertices, x)=true);
      ListContainedEdges_3:=Filtered(ListEdges_3, x->IsSubset(ListVertices, x)=true);
      if Length(ListContainedEdges)<>Length(ListVertices) then
        Error("Violation of polytopality condition");
      fi;
      if Length(ListContainedEdges_3)=Length(ListVertices) then
        RecO:=OrbitWithAction(VectorPres.GRPperm, ListVertices, OnSets);
        for eElt in RecO.ListElement
        do
          ListEdgeRel:=List(ListContainedEdges, x->OnSets(x, eElt));
          len:=Length(ListEdgeRel);
          eEdgeVect:=ListWithIdenticalEntries(nbEdge,0);
          ListEdgeReorg:=[ListEdgeRel[1]];
          ListStatus:=Concatenation([1], ListWithIdenticalEntries(len-1, 0));
          for i in [2..len]
          do
            eVert:=ListEdgeReorg[i-1][2];
            iEdge:=First([1..len], x->ListStatus[x]=0 and Position(ListEdgeRel[x],eVert)<>fail);
            ListStatus[iEdge]:=1;
            eEdge:=ListEdgeRel[iEdge];
            if eEdge[1]=eVert then
              fEdge:=[eEdge[1], eEdge[2]];
            else
              fEdge:=[eEdge[2], eEdge[1]];
            fi;
            Add(ListEdgeReorg, fEdge);
          od;
          for eEdge in ListEdgeReorg
          do
            eVert:=eEdge[1];
            fVert:=eEdge[2];
            if eVert < fVert then
              eEdge:=[eVert, fVert];
              eSign:=1;
            else
              eEdge:=[fVert, eVert];
              eSign:=-1;
            fi;
            pos:=Position(ListEdges, eEdge);
            eEdgeVect[pos]:=eEdgeVect[pos] + eSign;
          od;
          if eEdgeVect*ListEdgeVect<>ListWithIdenticalEntries(nbVert,0) then
            Error("Not a cycle B");
          fi;
          Add(TheSpannB, eEdgeVect);
        od;
      fi;
    od;
    Print("|TheSpannB|=", Length(TheSpannB), "\n");
    TheSpann:=Concatenation(TheSpannA, TheSpannB);
    if Length(TheSpann)=0 then
      rnkSpann:=0;
    else
      rnkSpann:=RankMat(TheSpann);
    fi;
    if Length(TheKernel)=0 then
      rnkKernel:=0;
    else
      rnkKernel:=RankMat(TheKernel);
    fi;
    if rnkSpann<>rnkKernel then
      return rec(answer:="find a violation to equality");
    fi;
    return rec(answer:="all correct");
  end;
  GetBelt_Equivariant:=function()
    ComputeBeltOrbit();
    return ListBeltOrbits;
  end;
  GetVectorAndRepresentation:=function()
    local ListFacetVect, GRPanti, ListVectOrbit, eOrb, eVect, O, ListPair, FullOrbRed, FuncGetPermutation, ListMatrGens, ListPermGens, GRPperm;
    ListFacetVect:=[];
    GRPanti:=Group([-IdentityMat(n)]);
    ListVectOrbit:=[];
    for eOrb in VoronoiFacetInequalities
    do
      O:=Orbit(DataLattice.PointGRP, eOrb.eVect, OnPoints);
      ListPair:=Orbits(GRPanti, O, OnPoints);
      FullOrbRed:=List(ListPair, x->x[1]);
      Append(ListFacetVect, FullOrbRed);
      Add(ListVectOrbit, FullOrbRed);
    od;
    FuncGetPermutation:=function(eMat)
      local eList;
      eList:=List(ListFacetVect, x->GetPositionAntipodal(ListFacetVect, x*eMat));
      return PermList(eList);
    end;
    ListMatrGens:=GeneratorsOfGroup(DataLattice.PointGRP);
    ListPermGens:=List(ListMatrGens, FuncGetPermutation);
    GRPperm:=Group(ListPermGens);
    return rec(GRPperm:=GRPperm,
               ListVectOrbit:=ListVectOrbit,
               FuncGetPermutation:=FuncGetPermutation,
               ListVectRed:=ListFacetVect);
  end;
  ComputeBeltAndBeltData:=function()
    local O1, FuncInsertBelt, eO1, idx1, eStab, eDiff, O2, eO2, idx2, eDiffVect, idx3, eSet;
    if HasFullBelt=true then
      return;
    fi;
    HasFullBelt:=true;
    O1:=Orbits(VectorPres.GRPperm, [1..Length(VectorPres.ListVectRed)], OnPoints);
    ListBelt:=[];
    ListBeltData:=[];
    FuncInsertBelt:=function(eSet)
      local TheO;
      if Position(ListBelt, eSet)<>fail then
        return;
      fi;
      TheO:=Orbit(VectorPres.GRPperm, eSet, OnSets);
      Append(ListBelt, TheO);
      Add(ListBeltData, rec(OrbSize:=Length(TheO), LVect:=VectorPres.ListVectRed{eSet}));
    end;
    for eO1 in O1
    do
      idx1:=eO1[1];
      eStab:=Stabilizer(VectorPres.GRPperm, idx1, OnPoints);
      eDiff:=Difference([1..Length(VectorPres.ListVectRed)], [idx1]);
      O2:=Orbits(eStab, eDiff, OnPoints);
      for eO2 in O2
      do
        idx2:=eO2[1];
        eDiffVect:=VectorPres.ListVectRed[idx1] - VectorPres.ListVectRed[idx2];
        idx3:=GetPositionAntipodal(VectorPres.ListVectRed, eDiffVect);
        if idx3<>fail then
          eSet:=Set([idx1, idx2, idx3]);
          FuncInsertBelt(eSet);
        fi;
        eDiffVect:=VectorPres.ListVectRed[idx1] + VectorPres.ListVectRed[idx2];
        idx3:=GetPositionAntipodal(VectorPres.ListVectRed, eDiffVect);
        if idx3<>fail then
          eSet:=Set([idx1, idx2, idx3]);
          FuncInsertBelt(eSet);
        fi;
      od;
    od;
  end;
  GetBeltAndBeltData:=function()
    ComputeBeltAndBeltData();
    return rec(ListBelt:=ListBelt, ListBeltData:=ListBeltData);
  end;
  VectorPres:=GetVectorAndRepresentation();
  ComputeFreeVector:=function()
    if HasFreeVector=true then
      return;
    fi;
    HasFreeVector:=true;
    ComputeBeltAndBeltData();
    ListFreeVectors:=FuncDirectEnumerationFreeVector(VectorPres.GRPperm, VectorPres.ListVectRed, ListBelt);
  end;
  FuncGetAllFreeVectors:=function()
    local ListFreeVect, eOrb, eListSet, eSet, VectorSet, NSP, eVect, ListPermGens, eList, PermGRPfree, FuncGetPermutation, eRecFree, ListMatrGens, phi;
    ComputeFreeVector();
    ComputeBeltAndBeltData();
    ListFreeVect:=[];
    for eOrb in ListFreeVectors
    do
      eListSet:=Orbit(VectorPres.GRPperm, eOrb.MatchedVectors, OnSets);
      for eSet in eListSet
      do
        VectorSet:=VectorPres.ListVectRed{eSet};
        NSP:=NullspaceMat(TransposedMat(VectorSet));
        if Length(NSP)<>1 then
          Error("We have a length problem in Free vector enumeration");
        fi;
        eVect:=RemoveFraction(NSP[1]*Inverse(DataLattice.GramMat));
        Add(ListFreeVect, eVect);
      od;
    od;
    FuncGetPermutation:=function(eMat)
      local eList;
      eList:=List(ListFreeVect, x->GetPositionAntipodal(ListFreeVect, x*eMat));
      return PermList(eList);
    end;
    ListMatrGens:=GeneratorsOfGroup(DataLattice.PointGRP);
    ListPermGens:=List(ListMatrGens, FuncGetPermutation);
    PermGRPfree:=Group(ListPermGens);
    phi:=GroupHomomorphismByImagesNC(DataLattice.PointGRP, PermGRPfree, ListMatrGens, ListPermGens);
    return rec(GramMat:=DataLattice.GramMat,
               ListFreeVect:=ListFreeVect,
               ListMatrGens:=ListMatrGens,
               ListPermGens:=ListPermGens,
               PermGRPfree:=PermGRPfree,
               phi:=phi,
               FuncGetPermutation:=FuncGetPermutation);
  end;
  FuncPrintBeltInformation:=function(output)
    local nbOrb, iOrb, eOrb, V1, V2, V3, iFree, eFree, TheOrb, TheBasisSpace;
    ComputeFreeVector();
    AppendTo(output, "  ", Length(VectorPres.ListVectRed), " edges of Delaunay\n");
    nbOrb:=Length(VectorPres.ListVectOrbit);
    AppendTo(output, "  ", nbOrb, " orbits of edges\n");
    for iOrb in [1..nbOrb]
    do
      eOrb:=VectorPres.ListVectOrbit[iOrb];
      AppendTo(output, "    |O", iOrb, "|=", Length(eOrb), " V=", POL_VectorString(eOrb[1]), "\n");
    od;
    nbOrb:=Length(ListBeltData);
    AppendTo(output, "  ", nbOrb, "  orbits of belts\n");
    for iOrb in [1..nbOrb]
    do
      eOrb:=ListBeltData[iOrb];
      V1:=eOrb.LVect[1];
      V2:=eOrb.LVect[2];
      V3:=eOrb.LVect[3];
      AppendTo(output, "    |O", iOrb, "|=", eOrb.OrbSize, "  V1=", POL_VectorString(V1), " V2=", POL_VectorString(V2), " V3=", POL_VectorString(V3), "\n");
    od;
    AppendTo(output, "  ", Length(ListFreeVectors), " orbits of free vectors\n");
    for iFree in [1..Length(ListFreeVectors)]
    do
      eFree:=ListFreeVectors[iFree];
      TheOrb:=Orbit(VectorPres.GRPperm, eFree.MatchedVectors, OnSets);
      AppendTo(output, "    |O", iFree, "|=", Length(TheOrb), " |relV|=", Length(eFree.MatchedVectors));
      TheBasisSpace:=eFree.BasisSpace;
      if Length(TheBasisSpace)=1 then
        AppendTo(output, " V=", POL_VectorString(TheBasisSpace[1]), "\n");
      else
        AppendTo(output, " V=", TheBasisSpace, "\n");
      fi;
    od;
    AppendTo(output, "\n");
  end;
  TestVectorFreeness:=function(eVect)
    local eBelt, ListScal;
    ComputeBeltAndBeltData();
    for eBelt in ListBelt
    do
      ListScal:=List(eBelt, x->VectorPres.ListVectRed[x]*DataLattice.GramMat*eVect);
      if Position(ListScal, 0)=fail then
        return false;
      fi;
    od;
    return true;
  end;
  TestVectorScalCondition:=function(eVect)
    local ListScal, ListScalDiff, a;
    ListScal:=List(VectorPres.ListVectRed, x->x*DataLattice.GramMat*eVect);
    ListScalDiff:=Difference(Set(ListScal), [0]);
    if Length(ListScalDiff)=0 then
      return true;
    fi;
    a:=ListScalDiff[1];
    if ListScalDiff<>Set([a,-a]) and ListScalDiff<>[a] then
      return true;
    fi;
    return false;
  end;
  GetFreeVectors:=function()
    ComputeFreeVector();
    return ListFreeVectors;
  end;
  return rec(GetBelt_Equivariant:=GetBelt_Equivariant,
             VectorPres:=VectorPres,
             GetBeltAndBeltData:=GetBeltAndBeltData,
             GetFreeVectors:=GetFreeVectors,
             TestVectorScalCondition:=TestVectorScalCondition,
             TestVectorFreeness:=TestVectorFreeness,
             ComputeGarber_Gavrilyuk_Magazinov_Condition:=ComputeGarber_Gavrilyuk_Magazinov_Condition,
             FuncGetAllFreeVectors:=FuncGetAllFreeVectors,
             FuncPrintBeltInformation:=FuncPrintBeltInformation);
end;



DelaunayDescriptionStandard:=function(U)
  local TheGramMat, PointGRP, ThePrefix, IsSaving, KillingDelaunay, KillingAdjacency, MaximalMemorySave;
  if IsBound(U.GramMat)=true then
    TheGramMat:=U.GramMat;
  else
    Error("GramMatrix should have been defined");
  fi;
  if IsBound(U.PointGRP)=true then
    PointGRP:=U.PointGRP;
  else
    PointGRP:=MatrixAutomorphismGroupGramMatrix(TheGramMat);
  fi;
  if IsBound(U.ThePrefix)=true then
    ThePrefix:=U.ThePrefix;
  else
    ThePrefix:=Filename(POLYHEDRAL_tmpdir, "DualDesc/");
    Exec("mkdir -p ", ThePrefix);
  fi;
  if IsBound(U.IsSaving)=true then
    IsSaving:=U.IsSaving;
  else
    IsSaving:=false;
  fi;
  if IsBound(U.MaximalMemorySave)=true then
    MaximalMemorySave:=U.MaximalMemorySave;
  else
    MaximalMemorySave:=false;
  fi;
  if IsPositiveDefiniteSymmetricMatrix(TheGramMat)=false then
    Error("The matrix should be positive definite");
  fi;
  #
  # we decided to remove the IsTotalGroup option
  # because it causes huge slowdown.
  KillingDelaunay:=function(EXT)
    return false;
  end;
  KillingAdjacency:=function(EXT1, EXT2)
    return false;
  end;
  return DelaunayDescriptionStandardKernel(TheGramMat, PointGRP, ThePrefix, IsSaving, KillingDelaunay, KillingAdjacency, MaximalMemorySave);
end;


VerticesOfVoronoiPolytope:=function(DataLattice, DelaunayDatabase, TheVert)
  local TheInit, SoftComp;
  TheInit:=InitialPair(DataLattice, DelaunayDatabase, TheVert);
  SoftComp:=SoftComputation(DataLattice, DelaunayDatabase, TheInit.EXT, TheInit.StabEXT, TheInit.TheDel);
  return VoronoiPolytopeListVertices(DataLattice, DelaunayDatabase, TheInit.StabEXT, SoftComp);
end;

GetSym2Representation:=function(n, TheGRP)
  local MatDim, NewMatrixGens, eGen, eGenNew, i, eVect, eSymmMat, eImgSymmMat, NewMatrixGRP;
  MatDim:=n*(n+1)/2;
  NewMatrixGens:=[];
  for eGen in GeneratorsOfGroup(TheGRP)
  do
    eGenNew:=[];
    for i in [1..MatDim]
    do
      eVect:=ListWithIdenticalEntries(MatDim,0);
      eVect[i]:=1;
      eSymmMat:=VectorToSymmetricMatrix(eVect, n);
      eImgSymmMat:=eGen*eSymmMat*TransposedMat(eGen);
      Add(eGenNew, SymmetricMatrixToVector(eImgSymmMat));
    od;
    Add(NewMatrixGens, eGenNew);
  od;
  NewMatrixGRP:=Group(NewMatrixGens);
  SetSize(NewMatrixGRP, Order(TheGRP));
  return NewMatrixGRP;
end;


Lspace:=function(DataLattice, DelaunayDatabase)
  local n, TheCan, MatDim, TheBasisMatrix, TheVectorSpace, NewMatrixGRP, iOrb, ListEqua, ListEquaRed, NSPvector, TheVectorSpaceProv, EXT;
  n:=DataLattice.n;
  TheCan:=CanonicalSymmetricBasis(n);
  MatDim:=TheCan.MatDim;
  TheBasisMatrix:=TheCan.TheBasisMatrix;
  TheVectorSpace:=TheCan.TheVectorSpace;
  NewMatrixGRP:=GetSym2Representation(n, DataLattice.PointGRP);
  for iOrb in [1..DelaunayDatabase.FuncDelaunayGetNumber()]
  do
    EXT:=DelaunayDatabase.FuncDelaunayGetEXT(iOrb);
    ListEqua:=ListEqualitiesDelaunay(EXT, TheBasisMatrix);
    NSPvector:=NullspaceMat(TransposedMat(ListEqua));
    TheVectorSpaceProv:=rec(n:=MatDim, ListVect:=List(NSPvector, x->x*TheVectorSpace.ListVect));
    TheVectorSpace:=IntersectionOrbitSubspace(TheVectorSpaceProv, NewMatrixGRP);
    TheBasisMatrix:=List(TheVectorSpace.ListVect, x->VectorToSymmetricMatrix(x, n));
  od;
  return TheBasisMatrix;
end;


SymmetryBreakingDelaunayDecomposition:=function(TheDecompoBig, TheBigMatrGroup, TheSmallMatrGroup, BigInvariantBasis)
  local n, GetPermGroup, GetMatrGroup, TheBigPermGroup, TheSmallPermGroup, ListOrbitSmallDelaunay, ListEXTSmallPermStab, ListOrbitAdjacencies, ListIOrbitDelaunay, ListInfoAdjDCS, ListListBigMatrix, ListListDCS, idx, TotalListIndices, TotalListBigMatrix, ListBigMatrix, ListTheBigPermStabGrp, eOrbit, TheBigMatrStabGrp, TheRedBigMatrStabGrp, TheBigPermStabGrp, TheSmallPermStab, TheSmallMatrStab, eIso, eIsoRed, ListMatrGens, eGen, eTrans, TheEXTSmallMatrStab, TheEXTSmallPermStab, ListListAdjDCS, eOrb, AdjStabBig, ListAdjDCS, ListApp, ListDCS, ListIndices, eDCS, eSmallMat, eBigMat, EXT, TheCosMatrStab, phi, TheStabInfo, ListReturn, iDelaunay, ListAdjacencies, iOrbit, iOrbitAdj, eAdjPair, eInc, FromOrigBigMat, FromOrigSmallMat, FromOrigBigPerm, jOrbit, pos, jDelaunay, fBigMat, TheRecord, eList;
  n:=Length(TheDecompoBig[1].EXT[1])-1;
  if RankMat(BigInvariantBasis)<>n then
    Error("The invariant basis is not of full rank");
  fi;
  GetPermGroup:=function(EXT, TheMatrGroup)
    local ListPermGens, eGen;
    ListPermGens:=[];
    for eGen in GeneratorsOfGroup(TheMatrGroup)
    do
      eList:=List(EXT, x->Position(EXT, x*eGen));
      Add(ListPermGens, PermList(eList));
    od;
    return Group(ListPermGens);
  end;
  GetMatrGroup:=function(EXT, ThePermGroup)
    local ListMatrGens, eGen, eMat;
    ListMatrGens:=[];
    for eGen in GeneratorsOfGroup(ThePermGroup)
    do
      eMat:=FindTransformation(EXT, EXT, eGen);
      Add(ListMatrGens, eMat);
    od;
    return PersoGroupMatrix(ListMatrGens, Length(EXT[1]));
  end;
  TheBigPermGroup:=GetPermGroup(BigInvariantBasis, TheBigMatrGroup);
  TheSmallPermGroup:=GetPermGroup(BigInvariantBasis, TheSmallMatrGroup);
  ListOrbitSmallDelaunay:=[];
  ListEXTSmallPermStab:=[];
  ListOrbitAdjacencies:=[];
  ListIOrbitDelaunay:=[];
  ListInfoAdjDCS:=[];
  ListListBigMatrix:=[];
  ListListDCS:=[];
  idx:=0;
  TotalListIndices:=[];
  TotalListBigMatrix:=[];
  ListTheBigPermStabGrp:=[];
  for iOrbit in [1..Length(TheDecompoBig)]
  do
    eOrbit:=TheDecompoBig[iOrbit];
    TheBigMatrStabGrp:=Image(eOrbit.TheStab.PhiPermMat);
    TheRedBigMatrStabGrp:=Group(List(GeneratorsOfGroup(TheBigMatrStabGrp), x->FuncExplodeBigMatrix(x).MatrixTransformation));
    TheBigPermStabGrp:=GetPermGroup(BigInvariantBasis, TheRedBigMatrStabGrp);
    Add(ListTheBigPermStabGrp, TheBigPermStabGrp);
    TheSmallPermStab:=Intersection(TheBigPermStabGrp, TheSmallPermGroup);
    TheSmallMatrStab:=GetMatrGroup(BigInvariantBasis, TheSmallPermStab);
    eIso:=Isobarycenter(eOrbit.EXT);
    eIsoRed:=eIso{[2..n+1]};
    ListMatrGens:=[];
    for eGen in GeneratorsOfGroup(TheSmallMatrStab)
    do
      eTrans:=eIsoRed-eIsoRed*eGen;
      Add(ListMatrGens, FuncCreateBigMatrix(eTrans, eGen));
    od;
    TheEXTSmallMatrStab:=Group(ListMatrGens);
    TheEXTSmallPermStab:=GetPermGroup(eOrbit.EXT, TheEXTSmallMatrStab);
    Add(ListEXTSmallPermStab, TheEXTSmallPermStab);
    ListListAdjDCS:=[];
    for eOrb in eOrbit.Adjacencies
    do
      AdjStabBig:=Stabilizer(eOrbit.TheStab.PermutationStabilizer, eOrb.eInc, OnSets);
      ListAdjDCS:=DoubleCosets(eOrbit.TheStab.PermutationStabilizer, AdjStabBig, TheEXTSmallPermStab);
      ListApp:=List(ListAdjDCS, x->rec(ePerm:=Representative(x), eBigMat:=Image(eOrbit.TheStab.PhiPermMat, Representative(x))));
      Add(ListListAdjDCS, ListApp);
    od;
    Add(ListInfoAdjDCS, ListListAdjDCS);
    ListDCS:=DoubleCosets(TheBigPermGroup, TheBigPermStabGrp, TheSmallPermGroup);
    Add(ListListDCS, ListDCS);
    ListIndices:=[];
    ListBigMatrix:=[];
    for eDCS in ListDCS
    do
      idx:=idx+1;
      Add(ListIndices, idx);
      eSmallMat:=FindTransformation(BigInvariantBasis, BigInvariantBasis, Representative(eDCS));
      eTrans:=ListWithIdenticalEntries(n, 0);
      eBigMat:=FuncCreateBigMatrix(eTrans, eSmallMat);
      EXT:=List(eOrbit.EXT, x->x*eBigMat);
      Add(ListBigMatrix, eBigMat);
      Add(TotalListBigMatrix, eBigMat);
      TheCosMatrStab:=GetMatrGroup(EXT, TheEXTSmallPermStab);
      phi:=GroupHomomorphismByImagesNC(TheEXTSmallPermStab, TheCosMatrStab, GeneratorsOfGroup(TheEXTSmallPermStab), GeneratorsOfGroup(TheCosMatrStab));
      TheStabInfo:=rec(PermutationStabilizer:=TheEXTSmallPermStab, PhiPermMat:=phi);
      Add(ListOrbitSmallDelaunay, rec(EXT:=EXT, TheStab:=TheStabInfo));
      Add(ListIOrbitDelaunay, iOrbit);
    od;
    Add(TotalListIndices, ListIndices);
    Add(ListListBigMatrix, ListBigMatrix);
  od;
  ListReturn:=[];
  for iDelaunay in [1..Length(ListOrbitSmallDelaunay)]
  do
    ListAdjacencies:=[];
    iOrbit:=ListIOrbitDelaunay[iDelaunay];
    for iOrbitAdj in [1..Length(ListInfoAdjDCS[iOrbit])]
    do
      for eAdjPair in ListInfoAdjDCS[iOrbit][iOrbitAdj]
      do
        eInc:=OnSets(TheDecompoBig[iOrbit].Adjacencies[iOrbitAdj].eInc, eAdjPair.ePerm);
        FromOrigBigMat:=TheDecompoBig[iOrbit].Adjacencies[iOrbitAdj].eBigMat*eAdjPair.eBigMat*TotalListBigMatrix[iDelaunay];
        FromOrigSmallMat:=FuncExplodeBigMatrix(FromOrigBigMat).MatrixTransformation;
        FromOrigBigPerm:=PermList(List(BigInvariantBasis, x->Position(BigInvariantBasis, x*FromOrigSmallMat)));
        jOrbit:=TheDecompoBig[iOrbit].Adjacencies[iOrbitAdj].iDelaunay;
        if IsSubset(Set(TheDecompoBig[jOrbit].EXT*FromOrigBigMat), Set(ListOrbitSmallDelaunay[iDelaunay].EXT{eInc}))=false then
          Error("Debug from here");
        fi;
        eDCS:=DoubleCoset(ListTheBigPermStabGrp[jOrbit], FromOrigBigPerm, TheSmallPermGroup);
        pos:=Position(ListListDCS[jOrbit], eDCS);
        jDelaunay:=TotalListIndices[jOrbit][pos];
        fBigMat:=Inverse(ListListBigMatrix[jOrbit][pos])*FromOrigBigMat;
        Add(ListAdjacencies, rec(eInc:=eInc, iDelaunay:=jDelaunay, eBigMat:=fBigMat));
      od;
    od;
    TheRecord:=rec(EXT:=ListOrbitSmallDelaunay[iDelaunay].EXT, TheStab:=ListOrbitSmallDelaunay[iDelaunay].TheStab, Adjacencies:=ListAdjacencies);
    Add(ListReturn, TheRecord);
  od;
  return ListReturn;
end;



CheckCoherencySingleDelaunay:=function(GramMat, EXT, FindClosestElement)
  local n, CP, Vcent, reply, ListEXT;
  n:=Length(GramMat);
  CP:=CenterRadiusDelaunayPolytopeGeneral(GramMat, EXT);
  Vcent:=CP.Center{[2..n+1]};
  reply:=FindClosestElement(Vcent);
  if reply.TheNorm>CP.SquareRadius then
    return rec(reply:=false, reason:="Wrong nearest norm, too large");
  fi;
  if reply.TheNorm<CP.SquareRadius then
    return rec(reply:=false, reason:="Wrong nearest norm, too small");
  fi;
  ListEXT:=List(reply.ListVect, x->Concatenation([1], x));
  if Set(ListEXT)<>Set(EXT) then
    return rec(reply:=false, reason:="More points on the sphere");
  fi;
  return rec(reply:=true);
end;


CheckCoherencySingleDelaunaySimple:=function(GramMat, EXT)
  local FindClosestElement;
  FindClosestElement:=function(eVect)
    return CVPVallentinProgram(GramMat, eVect);
  end;
  return CheckCoherencySingleDelaunay(GramMat, EXT, FindClosestElement);
end;

CheckCoherencyDelaunayDecomposition:=function(DataLattice, DelaunayDatabase)
  local n, GramMat, EXT, CP, Vcent, reply, ListEXT, eAdj, test, eFac, EXTAdjacentDelaunay, ListP, EXTb, nbDel, iDel, ListAdj, EXTfac1, EXTfac2, TheStab, eGen, eMatr, eList, TheAnswer;
  n:=DataLattice.n;
  GramMat:=DataLattice.GramMat;
  nbDel:=DelaunayDatabase.FuncDelaunayGetNumber();
  for iDel in [1..nbDel]
  do
    EXT:=DelaunayDatabase.FuncDelaunayGetEXT(iDel);
    TheAnswer:=CheckCoherencySingleDelaunay(GramMat, EXT, DataLattice.FindClosestElement);
    if TheAnswer.reply=false then
      Error("Wrong Delaunay");
    fi;
    TheStab:=DelaunayDatabase.FuncDelaunayGetGroup(iDel);
    for eGen in GeneratorsOfGroup(TheStab.PermutationStabilizer)
    do
      eMatr:=Image(TheStab.PhiPermMat, eGen);
      eList:=List(EXT, x->Position(EXT, x*eMatr));
      if PermList(eList)<>eGen then
        Error("We have inconsistency at this point");
      fi;
      if DataLattice.TestBelonging(eMatr)=false then
        Error("We have a non stabilizing element");
      fi;
    od;
    ListAdj:=DelaunayDatabase.FuncDelaunayGetAdjacencies(iDel);
    for eAdj in ListAdj
    do
      EXTb:=DelaunayDatabase.FuncDelaunayGetEXT(eAdj.iDelaunay);
      EXTAdjacentDelaunay:=EXTb*eAdj.eBigMat;
      if RankMat(EXT{eAdj.eInc})<>n then
        Error("Rank incoherency of facet");
      fi;
      eFac:=FindFacetInequality(EXT, eAdj.eInc);
      ListP:=Filtered([1..Length(EXT)], x->Position(EXTAdjacentDelaunay, EXT[x])<>fail);
      EXTfac1:=Filtered(EXT, x->x*eFac=0);
      EXTfac2:=Filtered(EXTAdjacentDelaunay, x->x*eFac=0);
      if Set(EXTfac1)<>Set(EXTfac2) then
        Error("The face to face tesselation seems compromised");
      fi;
      if ListP<>eAdj.eInc then
        Error("Incoherency on this point for DelaunayCoherency check");
      fi;
      test:=First(EXTAdjacentDelaunay, x->x*eFac>0);
      if test<>fail then
        Error("Incoherency on adjacent delaunay");
      fi;
    od;
  od;
  return "seems correct";
end;



GetSimpleDelaunayDatabase:=function(DelCO)
  local FuncDelaunayGetEXT, FuncDelaunayGetAdjacencies, FuncDelaunayGetGroup, FuncDelaunayGetNumber, DelaunayDatabase;
  FuncDelaunayGetEXT:=function(iOrb)
    return DelCO[iOrb].EXT;
  end;
  FuncDelaunayGetAdjacencies:=function(iOrb)
    return DelCO[iOrb].Adjacencies;
  end;
  FuncDelaunayGetGroup:=function(iOrb)
    return DelCO[iOrb].TheStab;
  end;
  FuncDelaunayGetNumber:=function()
    return Length(DelCO);
  end;
  DelaunayDatabase:=rec();
  DelaunayDatabase.FuncDelaunayGetEXT:=FuncDelaunayGetEXT;
  DelaunayDatabase.FuncDelaunayGetAdjacencies:=FuncDelaunayGetAdjacencies;
  DelaunayDatabase.FuncDelaunayGetGroup:=FuncDelaunayGetGroup;
  DelaunayDatabase.FuncDelaunayGetNumber:=FuncDelaunayGetNumber;
  return DelaunayDatabase;
end;


CheckCoherencyDelaunayDecompositionGramMatDelCO:=function(GramMat, DelCO)
  local DataLattice, DelaunayDatabase, FindClosestElement, TestBelonging;
  FindClosestElement:=function(eVect)
    return CVPVallentinProgram(GramMat, eVect);
  end;
  TestBelonging:=function(eBigMat)
    local eMat;
    eMat:=FuncExplodeBigMatrix(eBigMat).MatrixTransformation;
    return IsIntegralMat(eMat);
  end;
  DataLattice:=rec();
  DataLattice.n:=Length(GramMat);
  DataLattice.GramMat:=GramMat;
  DataLattice.FindClosestElement:=FindClosestElement;
  DataLattice.TestBelonging:=TestBelonging;
  DelaunayDatabase:=GetSimpleDelaunayDatabase(DelCO);
  return CheckCoherencyDelaunayDecomposition(DataLattice, DelaunayDatabase);
end;




ComputeCoveringDensityFromDimDetCov:=function(TheDim, TheDet, TheCov)
  local TheFileInput, TheFileOutput, output, TheCommand, TheResult;
  TheFileInput:=Filename(POLYHEDRAL_tmpdir,"covdensityInput.txt");
  TheFileOutput:=Filename(POLYHEDRAL_tmpdir,"covdensityOutput.txt");
  RemoveFileIfExist(TheFileInput);
  RemoveFileIfExist(TheFileOutput);
  output:=OutputTextFile(TheFileInput, true);
  AppendTo(output, TheDim, "\n");
  AppendTo(output, TheDet, "\n");
  AppendTo(output, TheCov, "\n");
  CloseStream(output);
  #
  TheCommand:=Concatenation(FileCompCovDens, " ", TheFileInput, " ", TheFileOutput);
  Exec(TheCommand);
  TheResult:=ReadAsFunction(TheFileOutput)();
  RemoveFileIfExist(TheFileInput);
  RemoveFileIfExist(TheFileOutput);
  TheResult.TheDim:=TheDim;
  TheResult.TheDet:=TheDet;
  TheResult.TheCov:=TheCov;
  return TheResult;
end;

GetCentralDelaunay:=function(TheGramMat, InvariantBasis, PointGRP)
  local TheMod, TheDim, ListOrb, ListRec, eOrb, eVect, eCent, reply, EXT, TheDimSel, eRec, GetDefiningVector, ListPermGens, GRPinv, eList, eGen, ListOrbitDiagonal, FuncInsertDiagonal, aVect, bVect, DiagVect, TheDimDel;
  TheMod:=2;
  TheDim:=Length(TheGramMat);
  ListOrb:=ComputeOrbitsVectors(PointGRP, TheDim, TheMod);
  ListRec:=[];
  GetDefiningVector:=function(eVect)
    return List(InvariantBasis, x->x*TheGramMat*eVect);
  end;
  ListPermGens:=[];
  for eGen in GeneratorsOfGroup(PointGRP)
  do
    eList:=List(InvariantBasis, x->Position(InvariantBasis, x*eGen));
    Add(ListPermGens, PermList(eList));
  od;
  GRPinv:=Group(ListPermGens);
  ListOrbitDiagonal:=[];
  FuncInsertDiagonal:=function(eVect, EXT)
    local eCharVect, eRecord, test, eStab, eOrbSize, eNorm;
    eCharVect:=GetDefiningVector(eVect);
    for eRecord in ListOrbitDiagonal
    do
      test:=PermutedRepresentativeAction(GRPinv, eCharVect, eRecord.eCharVect);
      if test<>fail then
        return;
      fi;
    od;
    eStab:=PermutedStabilizer(GRPinv, eCharVect);
    eOrbSize:=Order(PointGRP)/Order(eStab);
    eNorm:=eVect*TheGramMat*eVect;
    Add(ListOrbitDiagonal, rec(eVect:=eVect, EXT:=EXT, eNorm:=eNorm, eCharVect:=eCharVect, eOrbSize:=eOrbSize));
  end;
  for eOrb in ListOrb
  do
    eVect:=eOrb.eVect;
    if eVect*eVect > 0 then
      eCent:=eVect/2;
      reply:=CVPVallentinProgram(TheGramMat, eCent);
      EXT:=List(reply.ListVect, x->Concatenation([1], x));
      TheDimDel:=RankMat(EXT)-1;
      for aVect in reply.ListVect
      do
        bVect:=2*eCent - aVect;
        DiagVect:=bVect - aVect;
        FuncInsertDiagonal(DiagVect, EXT);
      od;
      eRec:=rec(eVect:=eVect, EXT:=EXT, OrbitSize:=eOrb.OrbitSize, TheDimDel:=TheDimDel);
      Add(ListRec, eRec);
    fi;
  od;
  return rec(ListRec:=ListRec, ListOrbitDiagonal:=ListOrbitDiagonal);
end;


GetForbiddenSubsetMagazinov:=function(TheGramMat, GRP, ListFreeInformation, ListRelevantVector, ListOrbitDiagonal)
  local ListFreeCan, eRecFree, n, eFreeVect, ListScal, eDiff, LVal, eVal, eFreeCan, ListForbidden, FuncInsertForbidden, eOrbDiag, LinSpace, TheOrthD, TheOrthV, ListGreaterOne, ListZero, rnkDiff, eSet, TheUnion, eVectGreat, eSetForb, iSet;
  ListFreeCan:=[];
  eRecFree:=ListFreeInformation.FuncGetAllFreeVectors();
  n:=Length(TheGramMat);
  for eFreeVect in eRecFree.ListFreeVect
  do
    ListScal:=List(ListRelevantVector, x->x*TheGramMat*eFreeVect);
    eDiff:=Difference(Set(ListScal), [0]);
    LVal:=Filtered(eDiff, x->x>0);
    if Length(LVal)>1 then
      Error("Error in enumeration");
    fi;
    eVal:=LVal[1];
    eFreeCan:=eFreeVect/eVal;
    Add(ListFreeCan, eFreeCan);
  od;
  #
  ListForbidden:=[];
  FuncInsertForbidden:=function(eSet)
    local fSet, test;
    for fSet in ListForbidden
    do
      test:=RepresentativeAction(eRecFree.PermGRPfree, eSet, fSet, OnSets);
      if test<>fail then
        return;
      fi;
    od;
    Add(ListForbidden, eSet);
  end;
  for eOrbDiag in ListOrbitDiagonal
  do
    LinSpace:=List(eOrbDiag.EXT, x->x{[2..n+1]} - eOrbDiag.EXT[1]{[2..n+1]});
    TheOrthD:=NullspaceMat(TransposedMat(LinSpace*TheGramMat));
    TheOrthV:=NullspaceMat(TransposedMat([eOrbDiag.eVect*TheGramMat]));
    ListGreaterOne:=Filtered(ListFreeCan, x->AbsInt(x*TheGramMat*eOrbDiag.eVect)>1);
    ListZero:=Filtered(ListFreeCan, x->x*TheGramMat*eOrbDiag.eVect=0);
    #
    rnkDiff:=Length(TheOrthV) - Length(TheOrthD);
    for eSet in Combinations(ListZero, rnkDiff)
    do
      TheUnion:=Concatenation(eSet, TheOrthD);
      if RankMat(TheUnion)=n-1 then
        for eVectGreat in ListGreaterOne
        do
          eSetForb:=Concatenation(eSet, [eVectGreat]);
          iSet:=Set(List(eSetForb, x->Position(ListFreeCan, x)));
          FuncInsertForbidden(iSet);
        od;
      fi;
    od;
  od;
  return ListForbidden;
end;


DelaunayComputationStandardFunctions:=function(TheGramMat)
  local n, InvariantBasis, PointGRP, ThePrefix, IsSaving, KillingDelaunay, KillingAdjacency, DLPD, TheReply, GetQuantization, GetVoronoiVertices, GetFreeVectors, GetDelaunayDescription, GetRigidityDegree, GetRadiusInformations, GetListRadiuses, ComputeListRadiuses, ListRadius, IsComputedRadius, TestCoveringMaximality, TestCoveringPessimum, GetListTdesignDelaunays, GetMatrixGroup, GetOrbitDefiningVoronoiFacetInequalities, GetDLPD, IsComputedLspace, TheLspace, ComputeLspace, GetLspace, GetLatticeLtypeInfo, TestMorseFunction, ComputeListEutacticity, IsComputedEutacticity, ListEutacticity, GetListEutacticity, ListWeakEutacticity, GetListWeakEutacticity, ComputeListWeakEutacticity, IsComputedWeakEutacticity, GetInvariantBasis, GetNeighborhood, GetRecordOfDelaunay, VoronoiFacetInequalities, IsComputedFacetInequalities, ListFreeInformation, GetStronglyTransversal, ComputeVoronoiFacetInequalities, ComputeFreeVectors, IsComputedFreeVectors, HasStronglyTransversal, ComputeStronglyTransversal, ListStronglyTransversal, ComputeOrbitsForbiddenSubsets, HasForbiddenSubsets, GetOrbitsForbiddenSubsets, ListOrbitForbiddenSubsets, CheckDelaunayTesselation, FlagFunctions, GetSpaceGroup, MaximalMemorySave, GetInternationalTableGroupName, GetCoveringDensity, GetSingleDelaunayComplete, GetTotalNrDelaunay, GetListSizePolytope, GetListRankPolytope, GetListVolumePolytope, IsLatticeEutactic, __GetCentralDelaunay, IsComputedCentralDelaunay, ListCentralDelaunay, GetForbiddenMagazinov, ComputeCentralDelaunay, GetContainingCell, GetAllTranslationClassesDelaunay, GetAllContainingCells, GetDelaunayDescriptionSmallerGroup, GetOrbitCells, GetVoronoiVertices_V1, RecSVR, PrintOutputToFile, GetGraphOfPoints, GetAoverB, GetKdimensionalCells, GetMagazinovTwoDimensionalComplex;

  n:=Length(TheGramMat);
  InvariantBasis:=__ExtractInvariantZBasisShortVectorNoGroup(TheGramMat);
  Print("DelaunayComputationStandardFunctions, |InvariantBasis|=", Length(InvariantBasis), "\n");
  PointGRP:=ArithmeticAutomorphismMatrixFamily_HackSouvignier_V2("", [TheGramMat], InvariantBasis);
  RecSVR:=GetRecSVR(TheGramMat, PointGRP);
  ThePrefix:=Filename(POLYHEDRAL_tmpdir, "DualDesc/");
  Exec("mkdir -p ", ThePrefix);
  IsSaving:=false;
  IsComputedRadius:=false;
  IsComputedEutacticity:=false;
  IsComputedWeakEutacticity:=false;
  IsComputedLspace:=false;
  IsComputedFacetInequalities:=false;
  IsComputedFreeVectors:=false;
  IsComputedCentralDelaunay:=false;
  HasStronglyTransversal:=false;
  HasForbiddenSubsets:=false;
  MaximalMemorySave:=false;
  DLPD:=ForKernel_DataLatticePolyhedralDatabase(TheGramMat, PointGRP, ThePrefix, IsSaving, MaximalMemorySave, RecSVR);
  TheReply:=ComputeDelaunayDecomposition(DLPD.DataLattice, DLPD.DataPolyhedral, DLPD.DelaunayDatabase);
  GetSpaceGroup:=function()
    local NewListGen, i, eVect, eBigGen, eGen;
    NewListGen:=[];
    for i in [1..n]
    do
      eVect:=ListWithIdenticalEntries(n,0);
      eVect[i]:=1;
      eBigGen:=FuncCreateBigMatrix(eVect, IdentityMat(n));
      Add(NewListGen, eBigGen);
    od;
    for eGen in GeneratorsOfGroup(PointGRP)
    do
      eVect:=ListWithIdenticalEntries(n, 0);
      eBigGen:=FuncCreateBigMatrix(eVect, eGen);
      Add(NewListGen, eBigGen);
    od;
    return Group(NewListGen);
  end;
  GetRecordOfDelaunay:=function(EXTdelaunay)
    local nbDel, iDelaunay, TheEXT, TheStab, eEquiv;
    nbDel:=DLPD.DelaunayDatabase.FuncDelaunayGetNumber();
    for iDelaunay in [1..nbDel]
    do
      TheEXT:=DLPD.DelaunayDatabase.FuncDelaunayGetEXT(iDelaunay);
      TheStab:=DLPD.DelaunayDatabase.FuncDelaunayGetGroup(iDelaunay);
      eEquiv:=DLPD.DataLattice.FuncIsomorphismDelaunay(DLPD.DataLattice, TheEXT, EXTdelaunay, TheStab);
      if eEquiv<>false then
        return rec(eBigMat:=eEquiv, iDelaunay:=iDelaunay);
      fi;
    od;
    Error("Some Delaunay that was asked is not in database");
  end;
  GetTotalNrDelaunay:=function()
    local TheTotalNr, nbDel, iDelaunay, TheStab;
    TheTotalNr:=0;
    nbDel:=DLPD.DelaunayDatabase.FuncDelaunayGetNumber();
    for iDelaunay in [1..nbDel]
    do
      TheStab:=DLPD.DelaunayDatabase.FuncDelaunayGetGroup(iDelaunay);
      TheTotalNr:=TheTotalNr + Order(PointGRP)/Order(TheStab.PermutationStabilizer);
    od;
    return TheTotalNr;
  end;
  GetNeighborhood:=function(EXTdelaunay)
    local eRecordFirst, ListCenter, ListDone, ListRecord, FuncInsert, DoIncrement, GetAllAddedVertices, PrintStatistics, ListGeneration, iGeneration;
    eRecordFirst:=GetRecordOfDelaunay(EXTdelaunay);
    ListCenter:=[Isobarycenter(EXTdelaunay)];
    ListDone:=[0];
    ListRecord:=[eRecordFirst];
    ListGeneration:=[0];
    iGeneration:=0;
    FuncInsert:=function(NewRecord)
      local eCent;
      eCent:=Isobarycenter(DLPD.DelaunayDatabase.FuncDelaunayGetEXT(NewRecord.iDelaunay)*NewRecord.eBigMat);
      if Position(ListCenter, eCent)=fail then
        Add(ListDone, 0);
        Add(ListCenter, eCent);
        Add(ListRecord, NewRecord);
        Add(ListGeneration, iGeneration);
      fi;
    end;
    DoIncrement:=function()
      local nbNow, iRecord, eRecord, TheAdjacencies, TheStab, eAdj, O, ePerm, eMatrix, NewRecord;
      nbNow:=Length(ListCenter);
      iGeneration:=iGeneration+1;
      for iRecord in [1..nbNow]
      do
        if ListDone[iRecord]=0 then
          ListDone[iRecord]:=1;
          eRecord:=ListRecord[iRecord];
          TheAdjacencies:=DLPD.DelaunayDatabase.FuncDelaunayGetAdjacencies(eRecord.iDelaunay);
          TheStab:=DLPD.DelaunayDatabase.FuncDelaunayGetGroup(eRecord.iDelaunay);
          for eAdj in TheAdjacencies
          do
            O:=OrbitWithAction(TheStab.PermutationStabilizer, eAdj.eInc, OnSets);
            for ePerm in O.ListElement
            do
              eMatrix:=Image(TheStab.PhiPermMat, ePerm);
              NewRecord:=rec(iDelaunay:=eAdj.iDelaunay, eBigMat:=eAdj.eBigMat*eMatrix*eRecord.eBigMat);
              FuncInsert(NewRecord);
            od;
          od;
        fi;
      od;
    end;
    GetAllAddedVertices:=function()
      local ListAddedVertices, eRecord, TheEXT;
      ListAddedVertices:=[];
      for eRecord in ListRecord
      do
        TheEXT:=DLPD.DelaunayDatabase.FuncDelaunayGetEXT(eRecord.iDelaunay)*eRecord.eBigMat;
        ListAddedVertices:=Union(ListAddedVertices, TheEXT);
      od;
      return Difference(ListAddedVertices, Set(EXTdelaunay));
    end;
    PrintStatistics:=function()
      local ListDelaunay;
      Print("  iGeneration=", iGeneration, "\n");
      Print("  neigh size=", Collected(ListGeneration), "\n");
      ListDelaunay:=List(ListRecord, x->x.iDelaunay);
      Print("  ListDelaunay=", Collected(ListDelaunay), "\n");
      Print("  nbVert=", Length(GetAllAddedVertices()), "\n");
    end;
    return rec(DoIncrement:=DoIncrement,
               GetAllAddedVertices:=GetAllAddedVertices,
               PrintStatistics:=PrintStatistics);
  end;
  GetContainingCell:=function(eVert)
    local eRec, EXT, eEXT, GetOneShift, ListVect, TheRel;
    eEXT:=Concatenation([1], eVert);
    eRec:=rec(iDelaunay:=1, eBigMat:=IdentityMat(n+1));
    GetOneShift:=function(eRec)
      local EXT, TheAdjacencies, TheStab, eAdj, O, ePerm, eMatrix, fSet, eFAC;
      EXT:=DLPD.DelaunayDatabase.FuncDelaunayGetEXT(eRec.iDelaunay)*eRec.eBigMat;
      TheAdjacencies:=DLPD.DelaunayDatabase.FuncDelaunayGetAdjacencies(eRec.iDelaunay);
      TheStab:=DLPD.DelaunayDatabase.FuncDelaunayGetGroup(eRec.iDelaunay);
      for eAdj in TheAdjacencies
      do
        O:=OrbitWithAction(TheStab.PermutationStabilizer, eAdj.eInc, OnSets);
        for ePerm in O.ListElement
        do
          eMatrix:=Image(TheStab.PhiPermMat, ePerm);
          fSet:=OnSets(eAdj.eInc, ePerm);
          eFAC:=FindFacetInequality(EXT, fSet);
          if eFAC*eEXT < 0 then
            return rec(iDelaunay:=eAdj.iDelaunay, eBigMat:=eAdj.eBigMat*eMatrix*eRec.eBigMat);
          fi;
        od;
      od;
      Error("We should never reach that stage");
    end;
    while(true)
    do
      EXT:=DLPD.DelaunayDatabase.FuncDelaunayGetEXT(eRec.iDelaunay)*eRec.eBigMat;
      ListVect:=Concatenation(EXT, [-eEXT]);
      TheRel:=SearchPositiveRelationSimple(ListVect);
      if TheRel<>false then
        return eRec;
      fi;
      eRec:=GetOneShift(eRec);
    od;
  end;
  GetAllContainingCells:=function(eVert)
    local ListRec, eEXT, FuncInsert, IsFinished, eRec, TheAdjacencies, TheStab, eAdj, O, ePerm, eMatrix, fSet, eFAC, NewRec, EXT, nbRec, iRec;
    ListRec:=[];
    eEXT:=Concatenation([1], eVert);
    FuncInsert:=function(eRec)
      local iDelaunay, eBigMat, EXT, eIso, fRec, NewRec;
      iDelaunay:=eRec.iDelaunay;
      eBigMat:=eRec.eBigMat;
      EXT:=DLPD.DelaunayDatabase.FuncDelaunayGetEXT(iDelaunay)*eBigMat;
      eIso:=Isobarycenter(EXT);
      for fRec in ListRec
      do
        if fRec.eIso=eIso then
          return;
        fi;
      od;
      NewRec:=rec(iDelaunay:=iDelaunay, eBigMat:=eBigMat, EXT:=EXT, eIso:=eIso, Status:="NO");
      Add(ListRec, NewRec);
    end;
    FuncInsert(GetContainingCell(eVert));
    while(true)
    do
      nbRec:=Length(ListRec);
      IsFinished:=true;
      for iRec in [1..nbRec]
      do
        if ListRec[iRec].Status="NO" then
          ListRec[iRec].Status:="YES";
          IsFinished:=false;
          eRec:=ListRec[iRec];
          EXT:=DLPD.DelaunayDatabase.FuncDelaunayGetEXT(eRec.iDelaunay)*eRec.eBigMat;
          TheAdjacencies:=DLPD.DelaunayDatabase.FuncDelaunayGetAdjacencies(eRec.iDelaunay);
          TheStab:=DLPD.DelaunayDatabase.FuncDelaunayGetGroup(eRec.iDelaunay);
          for eAdj in TheAdjacencies
          do
            O:=OrbitWithAction(TheStab.PermutationStabilizer, eAdj.eInc, OnSets);
            for ePerm in O.ListElement
            do
              eMatrix:=Image(TheStab.PhiPermMat, ePerm);
              fSet:=OnSets(eAdj.eInc, ePerm);
              eFAC:=FindFacetInequality(EXT, fSet);
              if eFAC*eEXT = 0 then
                NewRec:=rec(iDelaunay:=eAdj.iDelaunay, eBigMat:=eAdj.eBigMat*eMatrix*eRec.eBigMat);
                FuncInsert(NewRec);
              fi;
            od;
          od;
        fi;
      od;
      if IsFinished then
        break;
      fi;
    od;
    return ListRec;
  end;
  GetQuantization:=function()
    local TheOrigin, TheInt;
    TheOrigin:=ListWithIdenticalEntries(n+1,0);
    TheOrigin[1]:=1;
    TheInt:=QuantizationIntegral(DLPD.DataLattice, DLPD.DelaunayDatabase, TheOrigin);
    if TheInt.TheVolume<>1 then
      Error("We have an inconsistency in volume integral computation");
    fi;
    if TheInt.TheBarycenter<>TheOrigin then
      Error("We have an inconsistency in barycenter integral computation");
    fi;
    return TheInt.SecMoment;
  end;
  GetAoverB:=function()
    local TheOrigin, TheInt, ListRadiuses, CovRad, AoverB;
    TheOrigin:=ListWithIdenticalEntries(n+1,0);
    TheOrigin[1]:=1;
    TheInt:=QuantizationIntegral(DLPD.DataLattice, DLPD.DelaunayDatabase, TheOrigin);
    if TheInt.TheVolume<>1 then
      Error("We have an inconsistency in volume integral computation");
    fi;
    if TheInt.TheBarycenter<>TheOrigin then
      Error("We have an inconsistency in barycenter integral computation");
    fi;
    ListRadiuses:=GetListRadiuses();
    CovRad:=Maximum(ListRadiuses);
    AoverB:=TheInt.SecMoment / CovRad;
    return AoverB;
  end;
  GetVoronoiVertices_V1:=function()
    local TheOrigin, preEXT, EXT, ListPermGen, eGen, eVect, eBigGen, ePerm, GRP;
    TheOrigin:=ListWithIdenticalEntries(n+1,0);
    TheOrigin[1]:=1;
    preEXT:=VerticesOfVoronoiPolytope(DLPD.DataLattice, DLPD.DelaunayDatabase, TheOrigin);
    EXT:=Set(preEXT);
    ListPermGen:=[];
    eVect:=ListWithIdenticalEntries(n,0);
    for eGen in GeneratorsOfGroup(PointGRP)
    do
      eBigGen:=FuncCreateBigMatrix(eVect, eGen);
      ePerm:=SortingPerm(EXT*eBigGen);
      Add(ListPermGen, ePerm);
    od;
    GRP:=Group(ListPermGen);
    return rec(EXT:=EXT, GRP:=GRP);
  end;
  GetVoronoiVertices:=function()
    local preFAC, preEXT, nbDel, iDelaunay, TheEXT, DDA, nbV, iExt, eAdj, eVect, O, CP, eEXT, eDiff, EXT, FAC, eCst, eFAC, GetGraph, GetCanonicalGraph, ListPermGen, eGen, ePerm, eList, GroupFac, GetSubordinationInformation, GetFaceLattice;
    preFAC:=[];
    preEXT:=[];
    nbDel:=DLPD.DelaunayDatabase.FuncDelaunayGetNumber();
    for iDelaunay in [1..nbDel]
    do
      TheEXT:=DLPD.DelaunayDatabase.FuncDelaunayGetEXT(iDelaunay);
      DDA:=DualDescriptionAdjacencies(TheEXT);
      nbV:=Length(TheEXT);
      #
      # pre facets of Voronoi
      #
      for iExt in [1..nbV]
      do
        for eAdj in Adjacency(DDA.SkeletonGraph, iExt)
        do
          eVect:=TheEXT[iExt]{[2..n+1]} - TheEXT[eAdj]{[2..n+1]};
          if Position(preFAC, eVect)=fail then
            O:=Orbit(PointGRP, eVect, OnPoints);
            Append(preFAC, O);
          fi;
        od;
      od;
      #
      # pre vertices of Voronoi
      #
      CP:=CenterRadiusDelaunayPolytopeGeneral(TheGramMat, TheEXT);
      for eEXT in TheEXT
      do
        eDiff:=CP.Center{[2..n+1]} - eEXT{[2..n+1]};
        if Position(preEXT, eDiff)=fail then
          O:=Orbit(PointGRP, eDiff, OnPoints);
          Append(preEXT, O);
        fi;
      od;
    od;
    EXT:=List(preEXT, x->Concatenation([1],x));
    FAC:=[];
    for eVect in preFAC
    do
      eCst:=eVect*TheGramMat*eVect;
      eFAC:=Concatenation([eCst], 2*eVect*TheGramMat);
      Add(FAC, eFAC);
    od;
    ListPermGen:=[];
    for eGen in GeneratorsOfGroup(PointGRP)
    do
      eList:=List(preFAC, x->Position(preFAC, x*eGen));
      ePerm:=PermList(eList);
      Add(ListPermGen, ePerm);
    od;
    GroupFac:=Group(ListPermGen);
    GetGraph:=function()
      local nbEXT, nbFAC, ThePartition, ListAdjacency, iEXT, iFAC, ListIdx;
      nbEXT:=Length(EXT);
      nbFAC:=Length(FAC);
      ThePartition:=[[1..nbEXT], [1+nbEXT..nbEXT+nbFAC]];
      ListAdjacency:=[];
      for iEXT in [1..nbEXT]
      do
        ListIdx:=Filtered([1..nbFAC], x->FAC[x]*EXT[iEXT]=0);
        Add(ListAdjacency, List(ListIdx, x->x+nbEXT));
      od;
      for iFAC in [1..nbFAC]
      do
        ListIdx:=Filtered([1..nbEXT], x->EXT[x]*FAC[iFAC]=0);
        Add(ListAdjacency, ListIdx);
      od;
      return rec(ListAdjacency:=ListAdjacency, ThePartition:=ThePartition);
    end;
    GetCanonicalGraph:=function()
      local eRec, CanonDesc;
      eRec:=GetGraph();
      CanonDesc:=CanonicalRepresentativeVertexColoredGraphAdjList(eRec.ListAdjacency, eRec.ThePartition);
      return GetMD5expressionOfGraph(CanonDesc);
    end;
    GetSubordinationInformation:=function()
      local FileI, FileO, FileErr, output, TheCommand, eSymbol;
      FileI:=Filename(POLYHEDRAL_tmpdir, "FileIn");
      FileO:=Filename(POLYHEDRAL_tmpdir, "FileOut");
      FileErr:=Filename(POLYHEDRAL_tmpdir, "FileErr");
      output:=OutputTextFile(FileI, true);
      AppendTo(output, Length(EXT), " ", Length(EXT[1]), "\n");
      WriteMatrix(output, EXT);
      AppendTo(output, Length(FAC), " ", Length(FAC[1]), "\n");
      WriteMatrix(output, FAC);
      CloseStream(output);
      #
      TheCommand:=Concatenation(FileCompEngelSymbol, " ", FileI, " ", FileO, " 2> ", FileErr);
      Exec(TheCommand);
      #
      eSymbol:=ReadAsFunction(FileO)();
      RemoveFileIfExist(FileI);
      RemoveFileIfExist(FileO);
      return eSymbol;
    end;
    GetFaceLattice:=function()
      local eSymbol;
      eSymbol:=GetCompleteListFaces(EXT, FAC);
      return rec(EXT:=EXT, FAC:=FAC, eSymbol:=eSymbol);
    end;
    return rec(GroupFac:=GroupFac,
               FAC:=FAC,
               EXT:=EXT,
               GetCanonicalGraph:=GetCanonicalGraph,
               GetFaceLattice:=GetFaceLattice,
               GetSubordinationInformation:=GetSubordinationInformation);
  end;
  GetKdimensionalCells:=function(k)
    local TheSpaceGroup, nbDel, iDelaunay, pos, ListDelaunayK, ListIsoK, TranslationCanonicalization, IsobarycenterModOne, EXT, FAC, EXTsub, GetOrbit, eSymbol, eSet, FuncInsert;
    TheSpaceGroup:=GetSpaceGroup();
    nbDel:=DLPD.DelaunayDatabase.FuncDelaunayGetNumber();
    pos:=n - k;
    ListDelaunayK:=[];
    ListIsoK:=[];
    TranslationCanonicalization:=function(EXTsub)
      local eIso, eTrans, i, eVal, eFrac;
      eIso:=Isobarycenter(EXTsub);
      eTrans:=[0];
      for i in [1..n]
      do
        eVal:=eIso[i+1];
        eFrac:=FractionModOne(eVal);
        eTrans[i+1]:=eFrac - eVal;
      od;
      return rec(EXT:=List(EXTsub, x->x+eTrans), eIso:=eIso + eTrans);
    end;
    IsobarycenterModOne:=function(eVect)
      return Concatenation([1], List([1..n], x->FractionModOne(eVect[x+1])));
    end;
    GetOrbit:=function(eRec)
      local ListEXT, ListIso, ListStatus, IsFinished, len, i, IsoImg1, IsoImg2, eRecImg, eGen;
      ListEXT:=[eRec.EXT];
      ListIso:=[eRec.eIso];
      ListStatus:=[0];
      while(true)
      do
        IsFinished:=true;
        len:=Length(ListEXT);
        for i in [1..len]
        do
          if ListStatus[i]=0 then
            ListStatus[i]:=1;
            IsFinished:=false;
            for eGen in GeneratorsOfGroup(TheSpaceGroup)
            do
              IsoImg1:=ListIso[i] * eGen;
              IsoImg2:=IsobarycenterModOne(IsoImg1);
              if Position(ListIso, IsoImg2)=fail then
                eRecImg:=TranslationCanonicalization(ListEXT[i] * eGen);
                Add(ListEXT, eRecImg.EXT);
                Add(ListIso, eRecImg.eIso);
                Add(ListStatus, 0);
              fi;
            od;
          fi;
        od;
        if IsFinished then
          break;
        fi;
      od;
      return rec(ListEXT:=ListEXT, ListIso:=ListIso);
    end;
    FuncInsert:=function(EXTsub)
      local eRec, SecRec;
      eRec:=TranslationCanonicalization(EXTsub);
      if Position(ListIsoK, eRec.eIso)<>fail then
        return;
      fi;
      SecRec:=GetOrbit(eRec);
      Append(ListDelaunayK, SecRec.ListEXT);
      Append(ListIsoK, SecRec.ListIso);
    end;
    for iDelaunay in [1..nbDel]
    do
      EXT:=DLPD.DelaunayDatabase.FuncDelaunayGetEXT(iDelaunay);
      FAC:=DualDescription(EXT);
      eSymbol:=GetCompleteListFaces(EXT, FAC);
      for eSet in eSymbol[pos]
      do
        EXTsub:=EXT{eSet};
        FuncInsert(EXTsub);
      od;
    od;
    return ListDelaunayK;
  end;
  GetMagazinovTwoDimensionalComplex:=function()
    local k, ListDel, ListParityClass, GetPosParityClass, ListTwoFaces, ListOctahedron_2faces_14_25_36, ListOctahedron_2faces_13_24_56, eDel, eVertS, eVertA, eVertB, eVertC, eVertD, eVertE, eVertF, pos1, pos2, pos3, pos4, pos5, pos6, eNodeS, eNodeA, eNodeB, eNodeC, eNodeD, LPos, DDA, eSkel, eDiff, LAdj, LAdjB, ListPair, LSet, eSet, EXTred, eVert;

    k:=3;
    ListDel:=GetKdimensionalCells(k);
    ListParityClass:=Filtered(BuildSet(n, [0,1/2]), x->Sum(x)>0);
    GetPosParityClass:=function(eVect)
      return Position(ListParityClass, List(eVect, FractionModOne));
    end;
    ListTwoFaces:=[];
    ListOctahedron_2faces_14_25_36:=[[1,2,3],[4,2,3],[1,5,3],[4,5,3],[1,2,6],[4,2,6],[1,5,6],[4,5,6]];
    ListOctahedron_2faces_13_24_56:=[[1,2,5],[3,2,5],[1,4,5],[3,4,5],[1,2,6],[3,2,6],[1,4,6],[3,4,6]];
    for eDel in ListDel
    do
      if Length(eDel)=4 then
# Tetrahedron SABC
        eVertS:=eDel[1]{[2..n+1]};
        eVertA:=eDel[2]{[2..n+1]};
        eVertB:=eDel[3]{[2..n+1]};
        eVertC:=eDel[4]{[2..n+1]};
        pos1:=GetPosParityClass((eVertS + eVertA)/2);
        pos2:=GetPosParityClass((eVertS + eVertB)/2);
        pos3:=GetPosParityClass((eVertS + eVertC)/2);
        pos4:=GetPosParityClass((eVertB + eVertC)/2);
        pos5:=GetPosParityClass((eVertA + eVertC)/2);
        pos6:=GetPosParityClass((eVertA + eVertB)/2);
        LPos:=[pos1, pos2, pos3, pos4, pos5, pos6];
        for eSet in ListOctahedron_2faces_14_25_36
        do
          Add(ListTwoFaces, Set(LPos{eSet}));
        od;
      fi;
      if Length(eDel)=5 then
# Pyramid SABCD
        EXTred:=ColumnReduction(eDel).EXT;
        DDA:=DualDescriptionAdjacencies(EXTred);
        eSkel:=DDA.SkeletonGraph;
        eNodeS:=First([1..5], x->Length(Adjacency(eSkel, x))=4);
        eDiff:=Difference([1..5],[eNodeS]);
        eNodeA:=eDiff[1];
        LAdj:=Adjacency(eSkel, eNodeA);
        LAdjB:=Difference(Set(LAdj), [eNodeS]);
        eNodeB:=LAdjB[1];
        eNodeD:=LAdjB[2];
        eNodeC:=Difference(eDiff, Set([eNodeA, eNodeB, eNodeD]))[1];
        eVertS:=eDel[eNodeS]{[2..n+1]};
        eVertA:=eDel[eNodeA]{[2..n+1]};
        eVertB:=eDel[eNodeB]{[2..n+1]};
        eVertC:=eDel[eNodeC]{[2..n+1]};
        eVertD:=eDel[eNodeD]{[2..n+1]};
        pos1:=GetPosParityClass((eVertS + eVertA)/2);
        pos2:=GetPosParityClass((eVertS + eVertB)/2);
        pos3:=GetPosParityClass((eVertS + eVertC)/2);
        pos4:=GetPosParityClass((eVertS + eVertD)/2);
        pos5:=GetPosParityClass((eVertA + eVertB)/2);
        pos6:=GetPosParityClass((eVertB + eVertC)/2);
        LPos:=[pos1, pos2, pos3, pos4, pos5, pos6];
        for eSet in ListOctahedron_2faces_13_24_56
        do
          Add(ListTwoFaces, Set(LPos{eSet}));
        od;
      fi;
      if Length(eDel)=6 then
        eVert:=2*Isobarycenter(eDel);
        if IsIntegralVector(eVert) then
# Octahedron ABCDEF
          ListPair:=AntipodalDecomposition(eDel);
          eVertA:=eDel[ListPair[1][1]]{[2..n+1]};
          eVertB:=eDel[ListPair[2][1]]{[2..n+1]};
          eVertC:=eDel[ListPair[3][1]]{[2..n+1]};
          eVertD:=eDel[ListPair[1][2]]{[2..n+1]};
          eVertE:=eDel[ListPair[2][2]]{[2..n+1]};
          eVertF:=eDel[ListPair[3][2]]{[2..n+1]};
          pos1:=GetPosParityClass((eVertA + eVertB)/2);
          pos2:=GetPosParityClass((eVertA + eVertC)/2);
          pos3:=GetPosParityClass((eVertA + eVertE)/2);
          pos4:=GetPosParityClass((eVertA + eVertF)/2);
          pos5:=GetPosParityClass((eVertB + eVertC)/2);
          pos6:=GetPosParityClass((eVertB + eVertF)/2);
          LPos:=[pos1, pos2, pos3, pos4, pos5, pos6];
          for eSet in ListOctahedron_2faces_13_24_56
          do
            Add(ListTwoFaces, Set(LPos{eSet}));
          od;
        else
          LSet:=DualDescriptionSets(eDel);
          eSet:=First(LSet, x->Length(x)=3);
          eVertA:=eDel[eSet[1]]{[2..n+1]};
          eVertB:=eDel[eSet[2]]{[2..n+1]};
          eVertC:=eDel[eSet[3]]{[2..n+1]};
          pos1:=GetPosParityClass((eVertA + eVertB)/2);
          pos2:=GetPosParityClass((eVertA + eVertC)/2);
          pos3:=GetPosParityClass((eVertB + eVertC)/2);
          Add(ListTwoFaces, Set([pos1, pos2, pos3]));
        fi;
      fi;
    od;
    return Set(ListTwoFaces);
  end;
  ComputeFreeVectors:=function()
    local TheOrigin;
    if IsComputedFreeVectors=true then
      return;
    fi;
    ComputeVoronoiFacetInequalities();
    TheOrigin:=ListWithIdenticalEntries(n+1,0);
    TheOrigin[1]:=1;
    ListFreeInformation:=FreenessBeltListing(DLPD.DataLattice, DLPD.DelaunayDatabase, TheOrigin, VoronoiFacetInequalities);
    IsComputedFreeVectors:=true;
  end;
  GetForbiddenMagazinov:=function()
    local ListOrbitDiagonal, eRec, ListRelevantVector;
    ComputeCentralDelaunay();
    ListOrbitDiagonal:=ListCentralDelaunay.ListOrbitDiagonal;
    ComputeFreeVectors();
    eRec:=GetOrbitDefiningVoronoiFacetInequalities();
    ListRelevantVector:=eRec.GetCompleteListFacetDefining().ListVectors;
    return GetForbiddenSubsetMagazinov(TheGramMat, PointGRP, ListFreeInformation, ListRelevantVector, ListOrbitDiagonal);
  end;
  GetFreeVectors:=function()
    ComputeFreeVectors();
    return ListFreeInformation;
  end;
  GetDelaunayDescription:=function()
    return DLPD.DelaunayDatabase.FuncReturnCompleteDescription();
  end;
  GetDelaunayDescriptionSmallerGroup:=function(TheSmallMatrGroup)
    local DelCO;
    DelCO:=DLPD.DelaunayDatabase.FuncReturnCompleteDescription();
    return SymmetryBreakingDelaunayDecomposition(DelCO, PointGRP, TheSmallMatrGroup, InvariantBasis);
  end;
  GetSingleDelaunayComplete:=function(iOrb)
    return DLPD.DelaunayDatabase.FuncReturnSingleDelaunayComplete(iOrb);
  end;
  ComputeLspace:=function()
    if IsComputedLspace=true then
      return;
    fi;
    TheLspace:=Lspace(DLPD.DataLattice, DLPD.DelaunayDatabase);
    IsComputedLspace:=true;
  end;
  GetLspace:=function()
    ComputeLspace();
    return TheLspace;
  end;
  GetRigidityDegree:=function()
    ComputeLspace();
    return Length(TheLspace);
  end;
  GetLatticeLtypeInfo:=function()
    local eCase, SymGrp, ReducedGroup, RedDecompo, ListIneqs;
    ComputeLspace();
    eCase:=rec(Basis:=TheLspace, SuperMat:=TheGramMat, BravaisSpace:=false);
    SymGrp:=Group([-IdentityMat(n)]);
    ReducedGroup:=__FindFullSymmetrySpace(eCase, SymGrp);
    eCase.SymmGrpPtWs:=ReducedGroup;
    RedDecompo:=SymmetryBreakingDelaunayDecomposition(DLPD.DelaunayDatabase.FuncReturnCompleteDescription(), PointGRP, ReducedGroup, InvariantBasis);
    ListIneqs:=WriteFaceInequalities(RedDecompo, eCase);
    return rec(SymmGrpPtWs:=ReducedGroup, ListMat:=TheLspace, ListIneqs:=ListIneqs, eCase:=eCase);
  end;
  ComputeCentralDelaunay:=function()
    if IsComputedCentralDelaunay=true then
      return;
    fi;
    IsComputedCentralDelaunay:=false;
    ListCentralDelaunay:=GetCentralDelaunay(TheGramMat, InvariantBasis, PointGRP);
  end;
  __GetCentralDelaunay:=function()
    ComputeCentralDelaunay();
    return ListCentralDelaunay;
  end;
  ComputeListRadiuses:=function()
    local nbDel, iDelaunay, EXT, CP;
    if IsComputedRadius=true then
      return;
    fi;
    ListRadius:=[];
    nbDel:=DLPD.DelaunayDatabase.FuncDelaunayGetNumber();
    for iDelaunay in [1..nbDel]
    do
      EXT:=DLPD.DelaunayDatabase.FuncDelaunayGetEXT(iDelaunay);
      CP:=CenterRadiusDelaunayPolytopeGeneral(TheGramMat, EXT);
      Add(ListRadius, CP.SquareRadius);
    od;
    IsComputedRadius:=true;
  end;
  GetListRadiuses:=function()
    ComputeListRadiuses();
    return ListRadius;
  end;
  ComputeListEutacticity:=function()
    local nbDel, iDelaunay, EXT, GRP, ThePartition, TestEutact, CP;
    if IsComputedEutacticity=true then
      return;
    fi;
    nbDel:=DLPD.DelaunayDatabase.FuncDelaunayGetNumber();
    ListEutacticity:=[];
    for iDelaunay in [1..nbDel]
    do
      EXT:=DLPD.DelaunayDatabase.FuncDelaunayGetEXT(iDelaunay);
      GRP:=DLPD.DelaunayDatabase.FuncDelaunayGetGroup(iDelaunay);
      ThePartition:=Orbits(GRP.PermutationStabilizer, [1..Length(EXT)], OnPoints);
      TestEutact:=TestDelaunayEutacticityConditionPartitioned(EXT, ThePartition, TheGramMat);
      Add(ListEutacticity, TestEutact);
    od;
    IsComputedEutacticity:=true;
  end;
  GetListEutacticity:=function()
    ComputeListEutacticity();
    return ListEutacticity;
  end;
  IsLatticeEutactic:=function()
    local nbDel, IsEutacticLattice, eMax, iDelaunay;
    ComputeListRadiuses();
    ComputeListEutacticity();
    nbDel:=DLPD.DelaunayDatabase.FuncDelaunayGetNumber();
    eMax:=Maximum(ListRadius);
    IsEutacticLattice:=true;
    for iDelaunay in [1..nbDel]
    do
      if ListRadius[iDelaunay]=eMax then
        if ListEutacticity[iDelaunay]=false then
          IsEutacticLattice:=false;
        fi;
      fi;
    od;
    return IsEutacticLattice;
  end;
  GetListSizePolytope:=function()
    local nbDel, ListRankPolytope, iDelaunay, EXT;
    nbDel:=DLPD.DelaunayDatabase.FuncDelaunayGetNumber();
    ListRankPolytope:=[];
    for iDelaunay in [1..nbDel]
    do
      EXT:=DLPD.DelaunayDatabase.FuncDelaunayGetEXT(iDelaunay);
      Add(ListRankPolytope, Length(EXT));
    od;
    return ListRankPolytope;
  end;
  GetListVolumePolytope:=function()
    local nbDel, ListVolumePolytope, iDelaunay, EXT, TheVol, TheSum, eNb, TheStab;
    nbDel:=DLPD.DelaunayDatabase.FuncDelaunayGetNumber();
    ListVolumePolytope:=[];
    TheSum:=0;
    for iDelaunay in [1..nbDel]
    do
      EXT:=DLPD.DelaunayDatabase.FuncDelaunayGetEXT(iDelaunay);
      TheStab:=DLPD.DelaunayDatabase.FuncDelaunayGetGroup(iDelaunay);
      TheVol:=VolumeComputationPolytope(EXT);
      eNb:=Order(PointGRP)/Order(TheStab.PermutationStabilizer);
      TheSum:=TheSum + eNb*TheVol;
      Add(ListVolumePolytope, TheVol);
    od;
    if TheSum<>1 then
      Error("We have volume inconsistency");
    fi;
    return ListVolumePolytope;
  end;
  GetListRankPolytope:=function()
    local nbDel, ListRankPolytope, iDelaunay, EXT, eRank;
    nbDel:=DLPD.DelaunayDatabase.FuncDelaunayGetNumber();
    ListRankPolytope:=[];
    for iDelaunay in [1..nbDel]
    do
      EXT:=DLPD.DelaunayDatabase.FuncDelaunayGetEXT(iDelaunay);
      eRank:=RankPolytope(EXT);
      Add(ListRankPolytope, eRank);
    od;
    return ListRankPolytope;
  end;
  ComputeListWeakEutacticity:=function()
    local nbDel, iDelaunay, EXT, GRP, ThePartition, TestEutact, CP;
    if IsComputedWeakEutacticity=true then
      return;
    fi;
    nbDel:=DLPD.DelaunayDatabase.FuncDelaunayGetNumber();
    ListWeakEutacticity:=[];
    for iDelaunay in [1..nbDel]
    do
      EXT:=DLPD.DelaunayDatabase.FuncDelaunayGetEXT(iDelaunay);
      GRP:=DLPD.DelaunayDatabase.FuncDelaunayGetGroup(iDelaunay);
      ThePartition:=Orbits(GRP.PermutationStabilizer, [1..Length(EXT)], OnPoints);
      TestEutact:=TestDelaunayWeakEutacticityConditionPartitioned(EXT, ThePartition, TheGramMat);
      Add(ListWeakEutacticity, TestEutact);
    od;
    IsComputedWeakEutacticity:=true;
  end;
  GetListWeakEutacticity:=function()
    ComputeListWeakEutacticity();
    return ListWeakEutacticity;
  end;
  TestCoveringMaximality:=function()
    local MaxSqrRadius, nbDel, iDelaunay, EXT, LEutact;
    ComputeListRadiuses();
    MaxSqrRadius:=Maximum(ListRadius);
    nbDel:=DLPD.DelaunayDatabase.FuncDelaunayGetNumber();
    for iDelaunay in [1..nbDel]
    do
      if ListRadius[iDelaunay]=MaxSqrRadius then
        EXT:=DLPD.DelaunayDatabase.FuncDelaunayGetEXT(iDelaunay);
        if RankPolytope(EXT)<>1 then
          return false;
        fi;
      fi;
    od;
    LEutact:=GetListEutacticity();
    for iDelaunay in [1..nbDel]
    do
      if ListRadius[iDelaunay]=MaxSqrRadius then
        if LEutact[iDelaunay]=false then
          return false;
        fi;
      fi;
    od;
    return true;
  end;
  TestMorseFunction:=function()
    local MaxSqrRadius, nbDel, TheCan, TheBasisMatrix, TheVectorSpace, ListDimensions, ListRepresentativeSubspaces, iDelaunay, EXT, ListEqua, ListEquaRed, NSPvector, TheVectorSpaceProv, TestEutact, ThePartition, iDelaunaySelect, TheMaximalSpace, NewMatrixGRP, TheSpann, eVect, LEutact;
    ComputeListRadiuses();
    MaxSqrRadius:=Maximum(ListRadius);
    nbDel:=DLPD.DelaunayDatabase.FuncDelaunayGetNumber();
    # if they are not all eutactic, we are in trouble.
    TheCan:=CanonicalSymmetricBasis(n);
    TheBasisMatrix:=TheCan.TheBasisMatrix;
    TheVectorSpace:=TheCan.TheVectorSpace;
    ListDimensions:=[];
    ListRepresentativeSubspaces:=[];
    LEutact:=GetListEutacticity();
    for iDelaunay in [1..nbDel]
    do
      if ListRadius[iDelaunay]=MaxSqrRadius then
        EXT:=DLPD.DelaunayDatabase.FuncDelaunayGetEXT(iDelaunay);
        ListEqua:=ListEqualitiesDelaunay(EXT, TheBasisMatrix);
        ListEquaRed:=List(ListEqua, x->x{[2..Length(TheBasisMatrix)+1]});
        NSPvector:=NullspaceMat(TransposedMat(ListEquaRed));
        TheVectorSpaceProv:=rec(n:=TheVectorSpace.n, ListVect:=List(NSPvector, x->x*TheVectorSpace.ListVect));
        Add(ListRepresentativeSubspaces, TheVectorSpaceProv);
        Add(ListDimensions, Length(TheVectorSpaceProv.ListVect));
        TestEutact:=LEutact[iDelaunay];
        if TestEutact=false then
          return fail;
        fi;
      fi;
    od;
    iDelaunaySelect:=Position(ListDimensions, Maximum(ListDimensions));
    TheMaximalSpace:=ListRepresentativeSubspaces[iDelaunaySelect];
    NewMatrixGRP:=GetSym2Representation(n, PointGRP);
    for iDelaunay in [1..Length(ListRepresentativeSubspaces)]
    do
      TheSpann:=VectorSpaceSpannedUnionOrbit(ListRepresentativeSubspaces[iDelaunay], NewMatrixGRP);
      for eVect in TheSpann.ListVect
      do
        if SolutionMat(TheMaximalSpace.ListVect, eVect)=fail then
          return false;
        fi;
      od;
    od;
    return true;
  end;
  TestCoveringPessimum:=function()
    local MaxSqrRadius, nbDel, iDelaunay, EXT, GRP, TestEutact, ThePartition;
    ComputeListRadiuses();
    MaxSqrRadius:=Maximum(ListRadius);
    nbDel:=DLPD.DelaunayDatabase.FuncDelaunayGetNumber();
    for iDelaunay in [1..nbDel]
    do
      if ListRadius[iDelaunay]=MaxSqrRadius then
        EXT:=DLPD.DelaunayDatabase.FuncDelaunayGetEXT(iDelaunay);
        if Length(EXT)=Length(EXT[1]) then
          return false;
        fi;
      fi;
    od;
    ComputeListWeakEutacticity();
    for iDelaunay in [1..nbDel]
    do
      if ListRadius[iDelaunay]=MaxSqrRadius then
        if ListWeakEutacticity[iDelaunay]=false then
          return false;
        fi;
      fi;
    od;
    return true;
  end;
  CheckDelaunayTesselation:=function()
    CheckCoherencyDelaunayDecomposition(DLPD.DataLattice, DLPD.DelaunayDatabase);
  end;
  GetListTdesignDelaunays:=function()
    local nbDel, ListTdesigns, iDelaunay, EXT, GRP, CP, EXTred, tLevel;
    nbDel:=DLPD.DelaunayDatabase.FuncDelaunayGetNumber();
    ListTdesigns:=[];
    for iDelaunay in [1..nbDel]
    do
      EXT:=DLPD.DelaunayDatabase.FuncDelaunayGetEXT(iDelaunay);
      GRP:=DLPD.DelaunayDatabase.FuncDelaunayGetGroup(iDelaunay);
      CP:=CenterRadiusDelaunayPolytopeGeneral(TheGramMat, EXT);
      EXTred:=List(EXT, x->x{[2..n+1]}-CP.Center{[2..n+1]});
      tLevel:=SphericalDesignLevelGroup(EXTred, GRP.PermutationStabilizer, TheGramMat);
      Add(ListTdesigns, tLevel);
    od;
    return ListTdesigns;
  end;
  GetAllTranslationClassesDelaunay:=function()
    local nbDel, TotalListDelaunay, iDelaunay, EXT, eCentRed, eRecO, eElt, CP, eBigMat, ListRecInfos, eRecInfo;
    nbDel:=DLPD.DelaunayDatabase.FuncDelaunayGetNumber();
    TotalListDelaunay:=[];
    ListRecInfos:=[];
    for iDelaunay in [1..nbDel]
    do
      EXT:=DLPD.DelaunayDatabase.FuncDelaunayGetEXT(iDelaunay);
      CP:=CenterRadiusDelaunayPolytopeGeneral(TheGramMat, EXT);
      eCentRed:=VectorMod1(CP.Center{[2..n+1]});
      eRecO:=OrbitWithAction(PointGRP, eCentRed, OnClassesMod1);
      for eElt in eRecO.ListElement
      do
        eBigMat:=FuncCreateBigMatrix(ListWithIdenticalEntries(n,0),eElt);
        eRecInfo:=rec(iDelaunay:=iDelaunay, eBigMat:=eBigMat);
        Add(TotalListDelaunay, EXT*eBigMat);
        Add(ListRecInfos, eRecInfo);
      od;
    od;
    return rec(TotalListDelaunay:=TotalListDelaunay, ListRecInfos:=ListRecInfos);
  end;
  GetRadiusInformations:=function(FileName)
    local output;
    output:=OutputTextFile(FileName, true);
    RadiusesAndDelaunayCenterDistances(FileName, DLPD.DelaunayDatabase, DLPD.DataLattice);
    CloseStream(output);
  end;
  GetMatrixGroup:=function()
    return PointGRP;
  end;
  GetInvariantBasis:=function()
    return InvariantBasis;
  end;
  GetDLPD:=function()
    return DLPD;
  end;
  ComputeVoronoiFacetInequalities:=function()
    local GetDefiningVector, ListPermGens, eGen, eList, GRPinv, ListVectorRecords, FuncInsertVector, nbDel, iDelaunay, EXT, GRP, FuncAdj, eDiff, eDiffRed, eEdge, eIso, EXTcentered, ListGRA, GRA, ListTwoOrbit;
    if IsComputedFacetInequalities=true then
      return;
    fi;
    GetDefiningVector:=function(eVect)
      return List(InvariantBasis, x->x*TheGramMat*eVect);
    end;
    ListPermGens:=[];
    for eGen in GeneratorsOfGroup(PointGRP)
    do
      eList:=List(InvariantBasis, x->Position(InvariantBasis, x*eGen));
      Add(ListPermGens, PermList(eList));
    od;
    GRPinv:=Group(ListPermGens);
    ListVectorRecords:=[];
    FuncInsertVector:=function(eVect)
      local eCharVect, eRecord, test, eStab, eOrbSize, eNorm;
      eCharVect:=GetDefiningVector(eVect);
      for eRecord in ListVectorRecords
      do
        test:=PermutedRepresentativeAction(GRPinv, eCharVect, eRecord.eCharVect);
        if test<>fail then
          return;
        fi;
      od;
      eStab:=PermutedStabilizer(GRPinv, eCharVect);
      eOrbSize:=Order(PointGRP)/Order(eStab);
      eNorm:=eVect*TheGramMat*eVect;
      Add(ListVectorRecords, rec(eVect:=eVect, eNorm:=eNorm, eCharVect:=eCharVect, eOrbSize:=eOrbSize));
    end;
    nbDel:=DLPD.DelaunayDatabase.FuncDelaunayGetNumber();
    ListGRA:=[];
    for iDelaunay in [1..nbDel]
    do
      EXT:=DLPD.DelaunayDatabase.FuncDelaunayGetEXT(iDelaunay);
      eIso:=Isobarycenter(EXT);
      eIso[1]:=0;
      EXTcentered:=List(EXT, x->x-eIso);
      GRP:=DLPD.DelaunayDatabase.FuncDelaunayGetGroup(iDelaunay);
      FuncAdj:=function(S1,S2)
        return TestAdjacency(EXTcentered[S1], EXTcentered[S2], EXTcentered, []);
      end;
      ListTwoOrbit:=__RepresentativeOrbitTwoSet(GRP.PermutationStabilizer, [1..Length(EXT)]);
      GRA:=NullGraph(GRP.PermutationStabilizer, Length(EXT));
      for eEdge in ListTwoOrbit
      do
        if FuncAdj(eEdge[1], eEdge[2]) then
          eDiff:=EXT[eEdge[1]]-EXT[eEdge[2]];
          eDiffRed:=eDiff{[2..n+1]};
          FuncInsertVector(eDiffRed);
          AddEdgeOrbit(GRA, eEdge);
          AddEdgeOrbit(GRA, Reversed(eEdge));
        fi;
      od;
      Add(ListGRA, GRA);
    od;
    VoronoiFacetInequalities:=List(ListVectorRecords, x->rec(eVect:=x.eVect, eOrbSize:=x.eOrbSize, eNorm:=x.eNorm));
    IsComputedFacetInequalities:=true;
  end;
  GetOrbitDefiningVoronoiFacetInequalities:=function()
    local GetCompleteListFacetDefining, PrintInequalities;
    ComputeVoronoiFacetInequalities();
    GetCompleteListFacetDefining:=function()
      local ListVectors, ListIOrbit, ListNorm, nbOrb, iOrb, eRec, eO;
      ListVectors:=[];
      ListIOrbit:=[];
      ListNorm:=[];
      nbOrb:=Length(VoronoiFacetInequalities);
      for iOrb in [1..nbOrb]
      do
        eRec:=VoronoiFacetInequalities[iOrb];
        eO:=Orbit(PointGRP, eRec.eVect, OnPoints);
        Append(ListVectors, eO);
        Append(ListIOrbit, ListWithIdenticalEntries(Length(eO), iOrb));
        Append(ListNorm, ListWithIdenticalEntries(Length(eO), eRec.eNorm));
      od;
      return rec(ListVectors:=ListVectors,
                 ListIOrbit:=ListIOrbit,
                 ListNorm:=ListNorm);
    end;
    PrintInequalities:=function(output)
      local eRec, MaxNbChar, nbLine, iLine, eLine, eCol, eStr, nb, i;
      eRec:=GetCompleteListFacetDefining();
      MaxNbChar:=GetMaxNbCharMatrix(eRec.ListVectors);
      nbLine:=Length(eRec.ListVectors);
      for iLine in [1..nbLine]
      do
        eLine:=eRec.ListVectors[iLine];
        for eCol in eLine
        do
          eStr:=String(eCol);
          nb:=1+MaxNbChar - Length(eStr);
          for i in [1..nb]
          do
            AppendTo(output, " ");
          od;
          AppendTo(output, eStr);
        od;
        AppendTo(output, " iOrb=", eRec.ListIOrbit[iLine]);
        AppendTo(output, " norm=", eRec.ListNorm[iLine]);
        AppendTo(output, "\n");
      od;
    end;
    return rec(VoronoiFacetInequalities:=VoronoiFacetInequalities,
               GetCompleteListFacetDefining:=GetCompleteListFacetDefining,
               PrintInequalities:=PrintInequalities);
  end;
  ComputeStronglyTransversal:=function()
    if HasStronglyTransversal=true then
      return;
    fi;
    ListFreeInformation:=GetFreeVectors();
    ListStronglyTransversal:=SCV_EnumerationStronglyTransversal(DLPD.DataLattice, DLPD.DelaunayDatabase, ListFreeInformation);
    HasStronglyTransversal:=true;
  end;
  GetStronglyTransversal:=function()
    ComputeStronglyTransversal();
    return ListStronglyTransversal;
  end;
  ComputeOrbitsForbiddenSubsets:=function()
    local ListStronglyTransversalFaces, BeltFreeInformations;
    if HasForbiddenSubsets=true then
      return;
    fi;
    BeltFreeInformations:=GetFreeVectors();
    ListStronglyTransversalFaces:=GetStronglyTransversal();
    ListOrbitForbiddenSubsets:=FreedomStructure_GetForbiddenSubsetsFromFreeVectorStrongTransversal(DLPD.DataLattice, BeltFreeInformations, ListStronglyTransversalFaces);
    HasForbiddenSubsets:=true;
  end;
  GetOrbitsForbiddenSubsets:=function()
    ComputeOrbitsForbiddenSubsets();
    return ListOrbitForbiddenSubsets;
  end;
  FlagFunctions:=function()
    return DelaunayTesselation_DelaneySymbol(DLPD.DataLattice, DLPD.DelaunayDatabase);
  end;
  GetOrbitCells:=function()
    return DelaunayTesselation_GetOrbitCells(DLPD.DataLattice, DLPD.DelaunayDatabase);
  end;
  GetInternationalTableGroupName:=function()
    return Find3dimensionalSymmetry(GetSpaceGroup());
  end;
  GetCoveringDensity:=function()
    local ListRadiuses, TheDim, TheDet, TheCov;
    ListRadiuses:=GetListRadiuses();
    TheCov:=Maximum(ListRadiuses);
    TheDet:=DeterminantMat(TheGramMat);
    TheDim:=Length(TheGramMat);
    return ComputeCoveringDensityFromDimDetCov(TheDim, TheDet, TheCov);
  end;
  GetGraphOfPoints:=function(RecFuncLatt)
    local iA, nbTrans, GetPosition, GRA, eRec, ListRelevantVector, iTrans, eTrans, eVect, eSum, jTrans;
    if Length(RecFuncLatt.ListTrans[1])<>n then
      Error("TheLattice should have length n");
    fi;
    nbTrans:=Length(RecFuncLatt.ListTrans);
    Print("nbTrans=", nbTrans, "\n");
    GRA:=NullGraph(Group(()), nbTrans);
    eRec:=GetOrbitDefiningVoronoiFacetInequalities();
    ListRelevantVector:=eRec.GetCompleteListFacetDefining().ListVectors;
    Print("|ListRelevantVector|=", Length(ListRelevantVector), "\n");
    for iTrans in [1..nbTrans]
    do
      eTrans:=RecFuncLatt.ListTrans[iTrans];
      for eVect in ListRelevantVector
      do
        eSum:=eTrans + eVect;
        jTrans:=RecFuncLatt.GetPosition(eSum);
        AddEdgeOrbit(GRA, [iTrans, jTrans]);
        AddEdgeOrbit(GRA, [jTrans, iTrans]);
      od;
    od;
    return GRA;
  end;
  PrintOutputToFile:=function(output)
    local nbDel, MaxSquareRadius, iDelaunay, EXT, CP, GRP, TheAdjacencies;
    nbDel:=DLPD.DelaunayDatabase.FuncDelaunayGetNumber();
    AppendTo(output, "Number of Delaunay polytopes=", nbDel, "\n");
    MaxSquareRadius:=0;
    for iDelaunay in [1..nbDel]
    do
      EXT:=DLPD.DelaunayDatabase.FuncDelaunayGetEXT(iDelaunay);
      CP:=CenterRadiusDelaunayPolytopeGeneral(TheGramMat, EXT);
      GRP:=DLPD.DelaunayDatabase.FuncDelaunayGetGroup(iDelaunay);
      TheAdjacencies:=DLPD.DelaunayDatabase.FuncDelaunayGetAdjacencies(iDelaunay);
      AppendTo(output, "iDel=", iDelaunay, " |EXT|=", Length(EXT), " |GRP|=", Order(GRP.PermutationStabilizer), " |Adj|=", Length(TheAdjacencies), " cov=", CP.SquareRadius, "\n");
      MaxSquareRadius:=Maximum(MaxSquareRadius, CP.SquareRadius);
    od;
    AppendTo(output, "MaxSquareRadius=", MaxSquareRadius, "\n");
  end;
  return rec(GetDelaunayDescription:=GetDelaunayDescription,
             GetDelaunayDescriptionSmallerGroup:=GetDelaunayDescriptionSmallerGroup,
             GetRigidityDegree:=GetRigidityDegree,
             GetListRadiuses:=GetListRadiuses,
             GetGraphOfPoints:=GetGraphOfPoints,
             GetMagazinovTwoDimensionalComplex:=GetMagazinovTwoDimensionalComplex,
             GetDLPD:=GetDLPD,
             TestCoveringMaximality:=TestCoveringMaximality,
             TestCoveringPessimum:=TestCoveringPessimum,
             GetMatrixGroup:=GetMatrixGroup,
             GetCentralDelaunay:=__GetCentralDelaunay,
             GetInvariantBasis:=GetInvariantBasis,
             GetListVolumePolytope:=GetListVolumePolytope,
             GetListSizePolytope:=GetListSizePolytope,
             TestMorseFunction:=TestMorseFunction,
             GetOrbitCells:=GetOrbitCells,
             GetAoverB:=GetAoverB,
             GetAllContainingCells:=GetAllContainingCells,
             GetContainingCell:=GetContainingCell,
             GetInternationalTableGroupName:=GetInternationalTableGroupName,
             GetListTdesignDelaunays:=GetListTdesignDelaunays,
             GetListEutacticity:=GetListEutacticity,
             IsLatticeEutactic:=IsLatticeEutactic,
             GetKdimensionalCells:=GetKdimensionalCells,
             GetLspace:=GetLspace,
             GetTotalNrDelaunay:=GetTotalNrDelaunay,
             GetQuantization:=GetQuantization,
             GetCoveringDensity:=GetCoveringDensity,
             GetSingleDelaunayComplete:=GetSingleDelaunayComplete,
             FlagFunctions:=FlagFunctions,
             CheckDelaunayTesselation:=CheckDelaunayTesselation,
             GetRadiusInformations:=GetRadiusInformations,
             GetListRankPolytope:=GetListRankPolytope,
             GetVoronoiVertices:=GetVoronoiVertices,
             GetListEutacticity:=GetListEutacticity,
             GetListWeakEutacticity:=GetListWeakEutacticity,
             GetNeighborhood:=GetNeighborhood,
             GetRecordOfDelaunay:=GetRecordOfDelaunay,
             GetStronglyTransversal:=GetStronglyTransversal,
             GetOrbitsForbiddenSubsets:=GetOrbitsForbiddenSubsets,
             GetOrbitDefiningVoronoiFacetInequalities:=GetOrbitDefiningVoronoiFacetInequalities,
             GetFreeVectors:=GetFreeVectors,
             GetAllTranslationClassesDelaunay:=GetAllTranslationClassesDelaunay,
             GetForbiddenMagazinov:=GetForbiddenMagazinov,
             GetCoveringDensity:=GetCoveringDensity,
             PrintOutputToFile:=PrintOutputToFile);
end;

MagazinovMethodForForbiddenSubsets:=function(TheGramMat)
  local LFC, ListForbiddenMaga, ListBelt, eRecFree, ListForbiddenTotal, eSet, O, nbVect, IsSaving, ThePrefix, IsContainingForbidden, GetCorrectIncorrectSets, eRecMaximalMinimal, PreRecFree;
  LFC:=DelaunayComputationStandardFunctions(TheGramMat);
  ListForbiddenMaga:=LFC.GetForbiddenMagazinov();
  ListBelt:=LFC.GetFreeVectors();
  PreRecFree:=ListBelt.FuncGetAllFreeVectors();
  eRecFree:=rec(GramMat:=PreRecFree.GramMat,
                ListMatrGens:=PreRecFree.ListMatrGens,
                ListPermGens:=PreRecFree.ListPermGens,
                ListFreeVect:=PreRecFree.ListFreeVect,
                PermGRPfree:=PreRecFree.PermGRPfree);
  #
  ListForbiddenTotal:=[];
  for eSet in ListForbiddenMaga
  do
    O:=Orbit(eRecFree.PermGRPfree, eSet, OnSets);
    Append(ListForbiddenTotal, O);
  od;
  Print("|ListForbiddenTotal|=", Length(ListForbiddenTotal), "\n");
  #
  nbVect:=Length(eRecFree.ListFreeVect);
  Print("nbVect=", nbVect, "\n");
  IsSaving:=false;
  ThePrefix:="irrelevant";
  IsContainingForbidden:=function(eSet)
    local fSet;
    for fSet in ListForbiddenTotal
    do
      if IsSubset(eSet, fSet) then
        return true;
      fi;
    od;
    return false;
  end;
  GetCorrectIncorrectSets:=function(eSet)
    local eDiff, ListCorrect, ListIncorrect, idx, eSetTot;
    eDiff:=Difference([1..nbVect], eSet);
    ListCorrect:=[];
    ListIncorrect:=[];
    for idx in eDiff
    do
      eSetTot:=Union(eSet, [idx]);
      if IsContainingForbidden(eSetTot) then
        Add(ListIncorrect, idx);
      else
        Add(ListCorrect, idx);
      fi;
    od;
    return rec(ListCorrect:=ListCorrect, ListIncorrect:=ListIncorrect);
  end;
  Print("Now computing eRecMaximalMinimal\n");
  eRecMaximalMinimal:=MyEnumerationMaximalMinimalSpanning(IsSaving, ThePrefix, nbVect, eRecFree.PermGRPfree, GetCorrectIncorrectSets);
  Print("After computing eRecMaximalMinimal\n");
  return rec(eRecFree:=eRecFree, eRecMaximalMinimal:=eRecMaximalMinimal);
end;






OrbitFoldHomologyComputation:=function(kSought, ListOrbitByRank)
  local ListOperators, iRank, TheMat, eFace, eList, nbOrbPrec, nbEnt, iImg, iFace, ListHomologies, TheHomology, iFaceSec, SingleListPos, ListPositions, iPos, ListDimensions;
  ListDimensions:=[];
  ListPositions:=[];
  Add(ListDimensions, 0);
  for iRank in [2..kSought+3]
  do
    SingleListPos:=[];
    for iFace in [1..Length(ListOrbitByRank[iRank])]
    do
      eFace:=ListOrbitByRank[iRank][iFace];
      if eFace.IsHomologyInvar=true then
        Add(SingleListPos, iFace);
      fi;
    od;
    Add(ListPositions, SingleListPos);
    Add(ListDimensions, Length(SingleListPos));
  od;
  ListOperators:=[];
  for iRank in [2..kSought+3]
  do
    if iRank=2 then
      TheMat:=[];
      for iFace in [1..Length(ListOrbitByRank[iRank])]
      do
        Add(TheMat, []);
      od;
      Add(ListOperators, TheMat);
    else
      TheMat:=[];
      nbOrbPrec:=Length(ListOperators[iRank-2]);
      for eFace in ListOrbitByRank[iRank]
      do
        if eFace.IsHomologyInvar=true then
          eList:=ListWithIdenticalEntries(nbOrbPrec,0);
          nbEnt:=Length(eFace.BoundaryImage.ListIFace);
          for iImg in [1..nbEnt]
          do
            iFaceSec:=eFace.BoundaryImage.ListIFace[iImg];
            if ListOrbitByRank[iRank-1][iFaceSec].IsHomologyInvar=true then
              iPos:=Position(ListPositions[iRank-2], iFaceSec);
              eList[iPos]:=eList[iPos]+eFace.BoundaryImage.ListSign[iImg];
            fi;
          od;
          Add(TheMat, eList);
        fi;
      od;
      Add(ListOperators, TheMat);
    fi;
  od;
  ListHomologies:=[];
  for iRank in [0..kSought]
  do
    TheHomology:=GetQuotient(ListOperators[iRank+2], ListOperators[iRank+1], ListDimensions[iRank+3], ListDimensions[iRank+2], ListDimensions[iRank+1]);
    Add(ListHomologies, TheHomology);
  od;
  return ListHomologies;
end;






BoundaryOperatorsCellularDecomposition:=function(DataLattice, DelaunayDatabase, kSought)
  local n, TheVert, TheInit, ListOrbitByRank, iRank, TheComputedList, MyAction, FuncInsert, iFace, eFace, EXT, SoftComp, ListOrbit, eOrb, NewListOrbit, eOrbit, ListCentersM1, ListCentersM2, ListOccuringCoefficients, idx, eOrbitSmall, TheBoundary, eElt, iCenter, pos, ListSign, TheRetOrbit, eCenter, ListIFace, ListElt, TheReturnBoundary, TheCollect, TheListOccur, ThePossiblePos, iFaceSelect, IdxSel, eMulSign, eAddElt, ListElementM2, nbBound, iOrbitAsk, iFaceM1, eSign, eEltM2, ListOrbVertices, TheRec, eO, O, FuncSignatureDet, IsHomologyInvar, iOrbit;
  FuncSignatureDet:=function(EXT, eElt)
    local TheBasis, eRedMat, eMat, eLine;
    TheBasis:=RowReduction(EXT).EXT;
    eRedMat:=[];
    eMat:=[];
    for eLine in TheBasis
    do
      Add(eMat, SolutionMat(TheBasis, eLine*eElt));
    od;
    return DeterminantMat(eMat);
  end;
  IsHomologyInvar:=function(EXT, StabEXT)
    local eGen, TheDet;
    for eGen in GeneratorsOfGroup(StabEXT)
    do
      TheDet:=FuncSignatureDet(EXT, eGen);
      if TheDet=-1 then
        return false;
      fi;
    od;
    return true;
  end;
  n:=DataLattice.n;
  # An unstated assumption is that there is one orbit of point under
  # the crystallographic group automorphism.
  ListOrbitByRank:=[];
  ListOrbitByRank[1]:=[rec(EXT:=[], Center:=0, StabEXT:="/irrelevant/", BoundaryImage:="irrelevant", TheDel:="irrelevant", TheLevel:=-1)];
  O:=Orbits(DataLattice.GroupCoset, [1..Length(DataLattice.ListCoset)], OnPoints);
  ListOrbVertices:=[];
  for eO in O
  do
    TheVert:=DataLattice.ListCoset[eO[1]];
    TheInit:=InitialPair(DataLattice, DelaunayDatabase, TheVert);
    TheRec:=rec(EXT:=[TheVert], Center:=TheVert, StabEXT:=TheInit.StabEXT, BoundaryImage:=rec(ListIFace:=[1], ListSign:=[1], ListElt:=[IdentityMat(n+1)]), TheDel:=TheInit.TheDel, IsHomologyInvar:=true, TheLevel:=0);
    Add(ListOrbVertices, TheRec);
  od;
  Print("We have ", Length(O), " orbits of vertices\n");
  Add(ListOrbitByRank, ListOrbVertices);
  for iRank in [1..kSought+1]
  do
    TheComputedList:=[];
    MyAction:=function(EXT, eMat)
      return Set(EXT*eMat);
    end;
    FuncInsert:=function(EXTsmall, iFace, eOrb1)
      local eRecord1, TheEXT1, EXT1, eIso1inner, eIso1, EXT2, eIso2inner, eIso2, iOrbit2, eOrbit2, eEquiv, eOrbSmallBis, EXTsmallBis, EXTsmallImg, TheOrbSmall, NewListElement, eEquiv2, eOrbit1, ListPermGens, eList, eGen, GRPperm;
      eRecord1:=eOrb1.TheDel;
      TheEXT1:=DelaunayDatabase.FuncDelaunayGetEXT(eRecord1.iOrb);
      EXT1:=TheEXT1{eRecord1.eSet}*eRecord1.eMat;
      eIso1inner:=Isobarycenter(EXT1);
      Print("|EXTsmall|=", Length(EXTsmall), " |EXT1|=", Length(EXT1), "   |StabEXT|=", Order(eOrb1.StabEXT), " |DStabEXT|=", Order(eOrb1.DStabEXT), "\n");
      for iOrbit2 in [1..Length(TheComputedList)]
      do
        eOrbit2:=TheComputedList[iOrbit2];
        EXT2:=eOrbit2.EXT;
        eIso2inner:=Isobarycenter(EXT2);
        eEquiv:=DataLattice.FuncEquiv(EXT1, EXT2, eIso1inner, eIso2inner);
        if eEquiv<>false then
          EXTsmallImg:=Set(EXTsmall*eEquiv);
          TheOrbSmall:=OrbitWithAction(eOrbit2.StabEXT, EXTsmallImg, MyAction);
          NewListElement:=List(TheOrbSmall.ListElement, x->eEquiv*x);
          Add(TheComputedList[iOrbit2].ListOrbitSmall, rec(iFace:=iFace, ListElement:=NewListElement));
          return;
        fi;
      od;
      TheOrbSmall:=OrbitWithAction(eOrb1.StabEXT, Set(EXTsmall), MyAction);
      Print("|TheOrbSmall|=", Length(TheOrbSmall.ListElement), "  |StabEXT|=", Order(eOrb1.StabEXT), " |DStabEXT|=", Order(eOrb1.DStabEXT), "\n");
      ListPermGens:=[];
      for eGen in GeneratorsOfGroup(eOrb1.StabEXT)
      do
        eList:=List(EXT1, x->Position(EXT1, x*eGen));
        Add(ListPermGens, PermList(eList));
      od;
      GRPperm:=Group(ListPermGens);
      eOrbit1:=rec(EXT:=EXT1,
                   IsHomologyInvar:=IsHomologyInvar(EXT1, eOrb1.StabEXT),
                   StabEXT:=eOrb1.StabEXT, StabPerm:=GRPperm,
                   TheDel:=eRecord1,
                   ListOrbitSmall:=[rec(iFace:=iFace, ListElement:=TheOrbSmall.ListElement)]);
      Add(TheComputedList, eOrbit1);
    end;
    Print("Computing Delaunay cells of dimension ", iRank, "\n");
    for iFace in [1..Length(ListOrbitByRank[iRank+1])]
    do
      eFace:=ListOrbitByRank[iRank+1][iFace];
      SoftComp:=SoftComputation(DataLattice, DelaunayDatabase, eFace.EXT, eFace.StabEXT, eFace.TheDel);
      ListOrbit:=ListOrbitContainingEXT(DataLattice, DelaunayDatabase, eFace, SoftComp);
      for eOrb in ListOrbit
      do
        FuncInsert(eFace.EXT, iFace, eOrb);
      od;
    od;
    for iOrbit in [1..Length(TheComputedList)]
    do
      eOrbit:=TheComputedList[iOrbit];
      Print("|V", iOrbit, "|=", Length(eOrbit.EXT), " |Stab|=", Order(eOrbit.StabEXT), " inv=", eOrbit.IsHomologyInvar, " |OrbFacet|=");
      for eOrbitSmall in eOrbit.ListOrbitSmall
      do
        Print(Length(eOrbitSmall.ListElement), " ");
      od;
      Print("\n");
    od;
    # need to compute the signs now.
    Print("Now computing boundary operators\n");
    NewListOrbit:=[];
    for eOrbit in TheComputedList
    do
      ListCentersM1:=[];
      ListCentersM2:=[];
      ListElementM2:=[];
      ListIFace:=[];
      ListElt:=[];
      ListOccuringCoefficients:=[];
      idx:=0;
      for eOrbitSmall in eOrbit.ListOrbitSmall
      do
        iFaceM1:=eOrbitSmall.iFace;
        TheBoundary:=ListOrbitByRank[iRank+1][iFaceM1].BoundaryImage;
        for eElt in eOrbitSmall.ListElement
        do
          idx:=idx+1;
          Add(ListIFace, iFaceM1);
          Add(ListElt, eElt);
          Add(ListCentersM1, ListOrbitByRank[iRank+1][iFaceM1].Center*eElt);
          nbBound:=Length(TheBoundary.ListIFace);
          for iCenter in [1..nbBound]
          do
            eSign:=TheBoundary.ListSign[iCenter];
            eEltM2:=TheBoundary.ListElt[iCenter];
            eAddElt:=eEltM2*eElt;
            if iRank=1 then
              eCenter:="bckl";
            else
              eCenter:=ListOrbitByRank[iRank][TheBoundary.ListIFace[iCenter]].Center*eAddElt;
            fi;
            pos:=Position(ListCentersM2, eCenter);
            if pos=fail then
              Add(ListCentersM2, eCenter);
              Add(ListElementM2, eAddElt);
              Add(ListOccuringCoefficients, [rec(Sign:=eSign, idx:=idx)]);
            else
              if iRank<=2 then
                eMulSign:=1;
              else
                iOrbitAsk:=TheBoundary.ListIFace[iCenter];
                eMulSign:=FuncSignatureDet(ListOrbitByRank[iRank][iOrbitAsk].EXT, ListElementM2[pos]*eAddElt^(-1));
              fi;
              Add(ListOccuringCoefficients[pos], rec(Sign:=eMulSign*eSign, idx:=idx));
            fi;
          od;
        od;
      od;
      ListSign:=UntangleAllSigns(ListOccuringCoefficients, idx);
      TheReturnBoundary:=rec(ListIFace:=ListIFace, ListSign:=ListSign, ListElt:=ListElt);
      TheRetOrbit:=rec(EXT:=eOrbit.EXT, Center:=Isobarycenter(eOrbit.EXT), StabEXT:=eOrbit.StabEXT, BoundaryImage:=TheReturnBoundary, TheDel:=eOrbit.TheDel, TheLevel:=iRank, IsHomologyInvar:=eOrbit.IsHomologyInvar);
      Add(NewListOrbit, TheRetOrbit);
    od;
    #
    Add(ListOrbitByRank, NewListOrbit);
  od;
  return ListOrbitByRank;
end;




Periodic_DelaunayComputationStandardFunctions:=function(U)
  local ListCosets, TheGramMat, AffineCrystGroup, DLPD, KillingDelaunay, KillingAdjacency, TheReply, ThePrefix, IsSaving, GetDelaunayDescription, GetVoronoiVertices, GetQuantization, TheBoundary, LevelDoneBoundary, ComputeBoundary, GetBoundary, GetOrbitFoldHomology, CheckDelaunayTesselation, FlagFunctions, GetGroup, GetInternationalTableGroupName, HasDelaunaySkeleton, ListSkeleton, GetVertexNeighbors, ComputeDelaunaySkeleton;
  ListCosets:=U.ListCosets;
  TheGramMat:=U.GramMat;
  HasDelaunaySkeleton:=false;
  if IsBound(U.AffineCrystGroup)=true then
    AffineCrystGroup:=U.AffineCrystGroup;
  else
    AffineCrystGroup:=CrystallographicGroup(TheGramMat, ListCosets);
  fi;
  GetGroup:=function()
    local ListPtGens, ThePtGroup;
    ListPtGens:=List(GeneratorsOfGroup(AffineCrystGroup), x->FuncExplodeBigMatrix(x).MatrixTransformation);
    ThePtGroup:=Group(ListPtGens);
    return rec(AffineCrystGroup:=AffineCrystGroup, PointGroup:=ThePtGroup);
  end;
  ThePrefix:=Filename(POLYHEDRAL_tmpdir, "DualDesc/");
  Exec("mkdir -p ", ThePrefix);
  IsSaving:=false;
  LevelDoneBoundary:=-1;
  DLPD:=ForKernel_Periodic_DataLatticePolyhedralDatabase(TheGramMat, AffineCrystGroup, ListCosets, ThePrefix, IsSaving);
  if IsBound(U.KillingDelaunay)=true then
    DLPD.DataLattice.KillingDelaunay:=U.KillingDelaunay;
  else
    KillingDelaunay:=function(EXT)
      return false;
    end;
    DLPD.DataLattice.KillingDelaunay:=KillingDelaunay;
  fi;
  if IsBound(U.KillingAdjacency)=true then
    DLPD.DataLattice.KillingAdjacency:=U.KillingAdjacency;
  else
    KillingAdjacency:=function(EXT1, EXT2)
      return false;
    end;
    DLPD.DataLattice.KillingAdjacency:=KillingAdjacency;
  fi;
  TheReply:=ComputeDelaunayDecomposition(DLPD.DataLattice, DLPD.DataPolyhedral, DLPD.DelaunayDatabase);
  if TheReply<>"all was ok" then
    return false;
  fi;
  ComputeDelaunaySkeleton:=function()
    local nbDel, iDelaunay, TheEXT, TheStab, BoundingSet, TheSkel;
    if HasDelaunaySkeleton=false then
      HasDelaunaySkeleton:=true;
      nbDel:=DLPD.DelaunayDatabase.FuncDelaunayGetNumber();
      ListSkeleton:=[];
      for iDelaunay in [1..nbDel]
      do
        TheEXT:=DLPD.DelaunayDatabase.FuncDelaunayGetEXT(iDelaunay);
        TheStab:=DLPD.DelaunayDatabase.FuncDelaunayGetGroup(iDelaunay);
        BoundingSet:=[];
        TheSkel:=SkeletonGraph(TheStab.PermutationStabilizer, TheEXT, BoundingSet);
        Add(ListSkeleton, TheSkel);
      od;
    fi;
  end;
  GetDelaunayDescription:=function()
    return DLPD.DelaunayDatabase.FuncReturnCompleteDescription();
  end;
  GetVertexNeighbors:=function(eVert)
    local nbDel, ListAdjacent, iDelaunay, TheEXT, nbVert, eIso, eIsoRed, eRecO, nbCoset, iCoset, TheEXTimg, iVert, fVert, eDiff, iAdj, eVertAdj;
    ComputeDelaunaySkeleton();
    nbDel:=DLPD.DelaunayDatabase.FuncDelaunayGetNumber();
    ListAdjacent:=[];
    for iDelaunay in [1..nbDel]
    do
      TheEXT:=DLPD.DelaunayDatabase.FuncDelaunayGetEXT(iDelaunay);
      nbVert:=Length(TheEXT);
      eIso:=Isobarycenter(TheEXT);
      eIsoRed:=PeriodicVectorMod1(eIso);
      eRecO:=OrbitWithAction(AffineCrystGroup, eIsoRed, PeriodicOnClassesMod1);
      nbCoset:=Length(eRecO.ListCoset);
      for iCoset in [1..nbCoset]
      do
        TheEXTimg:=TheEXT*eRecO.ListCoset[iCoset];
        for iVert in [1..nbVert]
        do
          fVert:=TheEXTimg[iVert];
          eDiff:=fVert - eVert;
          if IsIntegralVector(eDiff)=true then
            for iAdj in Adjacency(ListSkeleton[iDelaunay], iVert)
            do
              eVertAdj:=TheEXTimg[iAdj] + eDiff;
              Add(ListAdjacent, eVertAdj);
            od;
          fi;
        od;
      od;
    od;
    return Set(ListAdjacent);
  end;
  GetQuantization:=function()
    local TotalVolume, TotalIntegral, O, eO, eVert, TheInt;
    TotalVolume:=0;
    TotalIntegral:=0;
    O:=Orbits(DLPD.DataLattice.GroupCoset, [1..Length(ListCosets)], OnPoints);
    for eO in O
    do
      eVert:=ListCosets[eO[1]];
      TheInt:=QuantizationIntegral(DLPD.DataLattice, DLPD.DelaunayDatabase, eVert);
      TotalVolume:=TotalVolume+Length(eO)*TheInt.TheVolume;
      TotalIntegral:=TotalIntegral+Length(eO)*TheInt.SecMoment;
    od;
    if TotalVolume<>1 then
      Error("We have an inconsistency in volume integral computation");
    fi;
    return TotalIntegral;
  end;
  GetVoronoiVertices:=function()
    local TheList, O, eO, eVertRemain, ListVertVoronoi, GetVoronoi;
    O:=Orbits(DLPD.DataLattice.GroupCoset, [1..Length(ListCosets)], OnPoints);
    TheList:=[];
    for eO in O
    do
      eVertRemain:=ListCosets[eO[1]];
      ListVertVoronoi:=VerticesOfVoronoiPolytope(DLPD.DataLattice, DLPD.DelaunayDatabase, eVertRemain);
      Add(TheList, rec(TheOrbit:=ListCosets{eO},
                       Representative:=eVertRemain,
                       ListVertVoronoi:=ListVertVoronoi));
    od;
    GetVoronoi:=function(eVert)
      local eVertRed, eDiff, eCase, eEquiv;
      eVertRed:=PeriodicVectorMod1(eVert);
      eDiff:=eVert-eVertRed;
      for eCase in TheList
      do
        eEquiv:=RepresentativeAction(AffineCrystGroup,
                      eCase.Representative, eVertRed, PeriodicOnClassesMod1);
        if eEquiv<>fail then
          return List(eCase.ListVertVoronoi*eEquiv, x->x+eDiff);
        fi;
      od;
      Print("Sorry we did not find eVert=", eVert, "\n");
      Print("to be equivalent to a coset element\n");
      Error("Please correct");
    end;
    return rec(TheList:=TheList, GetVoronoi:=GetVoronoi);
  end;
  ComputeBoundary:=function(kSought)
    if LevelDoneBoundary<kSought then
      TheBoundary:=BoundaryOperatorsCellularDecomposition(DLPD.DataLattice, DLPD.DelaunayDatabase, kSought);
      LevelDoneBoundary:=kSought;
    fi;
  end;
  GetBoundary:=function(kSought)
    ComputeBoundary(kSought);
    return TheBoundary;
  end;
  GetOrbitFoldHomology:=function(kSought)
    ComputeBoundary(kSought);
    return OrbitFoldHomologyComputation(kSought, TheBoundary);
  end;
  CheckDelaunayTesselation:=function()
    CheckCoherencyDelaunayDecomposition(DLPD.DataLattice, DLPD.DelaunayDatabase);
  end;
  FlagFunctions:=function()
    return DelaunayTesselation_DelaneySymbol(DLPD.DataLattice, DLPD.DelaunayDatabase);
  end;
  GetInternationalTableGroupName:=function()
    return Find3dimensionalSymmetry(AffineCrystGroup);
  end;
  return rec(GetVoronoiVertices:=GetVoronoiVertices,
             GetQuantization:=GetQuantization,
             GetBoundary:=GetBoundary,
             GetGroup:=GetGroup,
             GetOrbitFoldHomology:=GetOrbitFoldHomology,
             GetInternationalTableGroupName:=GetInternationalTableGroupName,
             FlagFunctions:=FlagFunctions,
             CheckDelaunayTesselation:=CheckDelaunayTesselation,
             DataLattice:=DLPD.DataLattice,
             GetVertexNeighbors:=GetVertexNeighbors,
             DelaunayDatabase:=DLPD.DelaunayDatabase,
             GetDelaunayDescription:=GetDelaunayDescription);
end;


Periodic_NonirreducibleDelaunayComputationStandardFunctions:=function(U)
  local ListCosets, TheGramMat, n, TransGroup, NewBasis, V, eTrans, NewGramMat, NewList1, NewList2, NewList3, ListFunc, GETvoronoi, GetVoronoi, GetVoronoiVertices, GetDelaunayEXT, ListOrigins, pos, i, iVert, eVert, MySetOrdPreserv, Ucall, KillingDelaunay, KillingAdjacency, GetVertexNeighbors;
  MySetOrdPreserv:=function(TheList)
    local len, i, RetList, pos;
    len:=Length(TheList);
    RetList:=[];
    for i in [1..len]
    do
      pos:=Position(RetList, TheList[i]);
      if pos=fail then
        Add(RetList, TheList[i]);
      fi;
    od;
    return RetList;
  end;
  ListCosets:=U.ListCosets;
  TheGramMat:=U.GramMat;
  CosetChecking(ListCosets, TheGramMat);
  n:=Length(TheGramMat);
  TransGroup:=GetTranslationGroup(ListCosets);
  NewBasis:=[];
  V:=ListWithIdenticalEntries(n+1,0);
  V[1]:=1;
  Add(NewBasis, V);
  for eTrans in TransGroup
  do
    Add(NewBasis, Concatenation([0], eTrans));
  od;
  NewGramMat:=RemoveFractionMatrix(TransGroup*TheGramMat*TransposedMat(TransGroup));
  NewList1:=List(ListCosets, x->SolutionMat(NewBasis, x));
  NewList2:=List(NewList1, PeriodicVectorMod1);
  NewList3:=MySetOrdPreserv(NewList2);
  ListOrigins:=[];
  for i in [1..Length(NewList3)]
  do
    Add(ListOrigins, []);
  od;
  for iVert in [1..Length(NewList2)]
  do
    eVert:=NewList2[iVert];
    pos:=Position(NewList3, eVert);
    Add(ListOrigins[pos], iVert);
  od;
  Ucall:=rec(ListCosets:=NewList3, GramMat:=NewGramMat);
  if IsBound(U.KillingDelaunay)=true then
    Ucall.KillingDelaunay:=U.KillingDelaunay;
  else
    KillingDelaunay:=function(EXT)
      return false;
    end;
    Ucall.KillingDelaunay:=KillingDelaunay;
  fi;
  if IsBound(U.KillingAdjacency)=true then
    Ucall.KillingAdjacency:=U.KillingAdjacency;
  else
    KillingAdjacency:=function(EXT1, EXT2)
      return false;
    end;
    Ucall.KillingAdjacency:=KillingAdjacency;
  fi;
  ListFunc:=Periodic_DelaunayComputationStandardFunctions(Ucall);
  if ListFunc=false then
    return false;
  fi;
  GetVoronoiVertices:=function()
    local TheList, TheC, eO, TheOrbit, eV, eRep, eListVertVoronoi, eNewO, GetVoronoi, pos;
    TheList:=[];
    TheC:=ListFunc.GetVoronoiVertices();
    for eO in TheC.TheList
    do
      TheOrbit:=[];
      for eV in eO.TheOrbit
      do
        pos:=Position(NewList3, eV);
        TheOrbit:=Union(TheOrbit, ListOrigins[pos]);
      od;
      eRep:=eO.Representative*NewBasis;
      eListVertVoronoi:=eO.ListVertVoronoi*NewBasis;
      eNewO:=rec(TheOrbit:=ListCosets{TheOrbit},
                 Representative:=eRep,
                 ListVertVoronoi:=eListVertVoronoi);
      Add(TheList, eNewO);
    od;
    GetVoronoi:=function(eVert)
      local NewCoord, ListVertVoronoi;
      NewCoord:=SolutionMat(NewBasis, eVert);
      ListVertVoronoi:=TheC.GetVoronoi(NewCoord);
      return ListVertVoronoi*NewBasis;
    end;
    return rec(TheList:=TheList, GetVoronoi:=GetVoronoi);
  end;
  GetDelaunayEXT:=function()
    local eOrbit, ListOrbit, EXT, EXTred, NewEXT;
    ListOrbit:=[];
    for eOrbit in ListFunc.GetDelaunayDescription()
    do
      NewEXT:=eOrbit.EXT*NewBasis;
      Add(ListOrbit, NewEXT);
    od;
    return ListOrbit;
  end;
  GetVertexNeighbors:=function(eVert)
    local eVertRed, ListAdjacent;
    eVertRed:=eVert*Inverse(NewBasis);
    ListAdjacent:=ListFunc.GetVertexNeighbors(eVertRed);
    return ListAdjacent*NewBasis;
  end;
  return rec(GetVoronoiVertices:=GetVoronoiVertices,
             FlagFunctions:=ListFunc.FlagFunctions,
             GetInternationalTableGroupName:=ListFunc.GetInternationalTableGroupName,
             CheckDelaunayTesselation:=ListFunc.CheckDelaunayTesselation,
             GetDelaunayEXT:=GetDelaunayEXT);
end;



GetVerticesAdjacentDelaunay:=function(GramMat, EXT, GRP)
  local ListOrbFac, LVERT, eInc, EXTadj, LnonOrb, GRPmat, ListSoughtVertices, eVert, O, ListMatGens, eMatrGen, eGen;
  ListOrbFac:=DualDescriptionStandard(EXT, GRP);
  LVERT:=[];
  for eInc in ListOrbFac
  do
    EXTadj:=FindAdjacentDelaunayPolytope(GramMat, EXT, eInc);
    Append(LVERT, Difference(Set(EXTadj), Set(EXT)));
  od;
  LnonOrb:=Set(LVERT);
  ListMatGens:=[];
  for eGen in GeneratorsOfGroup(GRP)
  do
    eMatrGen:=FindTransformation(EXT, EXT, eGen);
    if IsIntegralMat(eMatrGen)=false then
      Error("The matrix is not integral");
    fi;
    Add(ListMatGens, eMatrGen);
  od;
  GRPmat:=Group(ListMatGens);
  ListSoughtVertices:=[];
  while(true)
  do
    eVert:=LnonOrb[1];
    O:=Orbit(GRPmat, eVert);
    Append(ListSoughtVertices, O);
    LnonOrb:=Difference(LnonOrb, Set(O));
    if Length(LnonOrb)=0 then
      break;
    fi;
  od;
  Append(ListSoughtVertices, EXT);
  return ListSoughtVertices;
end;






#
#
# This code is for massive use of method6,
# i.e., it uses ISOM/AUTOM but requires knowing EXT.
#
# program writing is incomplete and at present frozen
#
M6_Formalism:=function(GramMat, InvariantBase)
  local MyStabilizer, MyEquivalence, M6__Action, M6__eElt__to__Matrix, M6__Stabilizer, M6__RepresentativeAction, M6__GroupUnion, M6__IndividualLifting, M6__LiftingOrbits, M6__PermGroupAction, M6__Order, M6__IsSubgroup, M6__Inverse, M6__Product, M6__GroupConjugacy, M6__TransformIncidenceList, M6__OrbitGroupFormalism, M6__BankKeyInformation, M6__BankCompleteInformation, M6__BankGetVertexSet, M6__BankGetGroup, M6__BankGetListObject, DIH_GRP, M6__BankGetForIsom;
  MyStabilizer:=function(EXT, ePoint)
    local TheGrp, NewListGens, eGen, eMat, eList;
    TheGrp:=M6_Stabilizer(GramMat, InvariantBase, EXT, ePoint);
    NewListGens:=[];
    for eGen in GeneratorsOfGroup(TheGrp)
    do
      eMat:=FuncExplodeBigMatrix(eGen).MatrixTransformation;
      eList:=List(InvariantBase, x->Position(InvariantBase, x*eMat));
      Add(NewListGens, rec(ePerm:=PermList(eList), eBigMat:=eGen));
    od;
    return NewListGens;
  end;
  MyEquivalence:=function(EXT1, EXT2, ePoint1, ePoint2)
    local TheEquiv, eMat, eList;
    TheEquiv:=M6_Equivalence(GramMat, InvariantBase, EXT1, EXT2, ePoint1, ePoint2);
    if TheEquiv=false then
      return false;
    fi;
    eMat:=FuncExplodeBigMatrix(TheEquiv).MatrixTransformation;
    eList:=List(InvariantBase, x->Position(InvariantBase, x*eMat));
    return rec(ePerm:=PermList(eList), eBigMat:=TheEquiv);
  end;
  M6__Stabilizer:=function(EXT, M6__Grp, Linc)
    local eCenter, fCenter;
    eCenter:=Isobarycenter(EXT{Linc});
    fCenter:=Isobarycenter(EXT);
    return MyStabilizer(EXT, (eCenter+fCenter)/2);
  end;
  M6__Order:=function(M6__Grp)
    return Order(M6__Grp);
  end;
  M6__IsSubgroup:=function(M6__Grp1, M6__Grp2)
    # we take some risk
    # the idea is that never we are in bad circumstances.
    # check with Coxeter_Lattice_Formalism, which has some checks.
    return true;
  end;
  M6__GroupUnion:=function(M6__Grp1, M6__Grp2)
    # again this is somewhat risky.
    # check with Coxeter_Lattice_Formalism, which has some checks.
    return M6__Grp1;
  end;
  M6__LiftingOrbits:=function(EXT, ListInc, M6__Small, M6__Big)
    local PermSmall, ePoint, PermBig, PermBigGens, MatBigGens, MatBig, phi, PartialNewList, StabBig, RealStabBig, PermStabBig, eDCS, ePerm, eInc, eMat, eImgInc;
    PermSmall:=Group(List(M6__Small, x->x.ePerm));
    #
    PermBigGens:=List(M6__Big, x->x.ePerm);
    PermBig:=Group(List(M6__Big, x->x.ePerm));
    MatBigGens:=List(M6__Big, x->x.eBigMat);
    MatBig:=Group(MatBigGens);
    #
    phi:=GroupHomomorphismByImagesNC(PermBig, MatBig, PermBigGens, MatBigGens);
    #
    PartialNewList:=[];
    for eInc in ListInc
    do
      ePoint:=(Isobarycenter(EXT)+Isobarycenter(EXT{eInc}))/2;
      RealStabBig:=MyStabilizer(EXT, ePoint);
      PermStabBig:=Group(List(RealStabBig, x->x.ePerm));
      for eDCS in DoubleCosets(PermBig, PermStabBig, PermSmall)
      do
        ePerm:=Representative(eDCS);
        eMat:=Image(phi, ePerm);
        eImgInc:=List(eInc, x->Position(EXT, EXT[x]*eMat));
        Add(PartialNewList, Set(eImgInc));
      od;
    od;
    return PartialNewList;
  end;
  M6__PermGroupAction:=function(ListEXT, M6__Grp)
    local TheStab, ListPermGens, eGen, eList;
    TheStab:=Group(List(M6__Grp, x->x.eBigMat));
    ListPermGens:=[];
    for eGen in TheStab
    do
      eList:=List(ListEXT, x->Position(ListEXT, x*eGen.eBigMat));
      Add(ListPermGens, PermList(eList));
    od;
    return Group(ListPermGens);
  end;
  M6__GroupConjugacy:=function(M6__Grp, eElt)
    local NewListGens, eGen;
    NewListGens:=[];
    for eGen in NewListGens
    do
      Add(NewListGens, rec(ePerm:=eElt.ePerm^(-1)*eGen.ePerm*eElt.ePerm, eBigMat:=Inverse(eElt.eBigMat)*eGen.eBigMat*eElt.eBigMat));
    od;
    return NewListGens;
  end;
  M6__TransformIncidenceList:=function(ListEXT1, ListEXT2, TheEquiv, ListListInc)
    local NewListListInc, eInc, fInc;
    NewListListInc:=[];
    for eInc in ListListInc
    do
      fInc:=Set(List(ListEXT1{eInc}, x->Position(ListEXT2, x*TheEquiv.eBigMat)));
      Add(NewListListInc, fInc);
    od;
    return NewListListInc;
  end;
  M6__OrbitGroupFormalism:=function(EXT, M6__Grp, Prefix, SavingTrigger)
    local FuncInvariant, FuncIsomorphy, FuncInvariantUpdate, OrderLincStabilizer;
    FuncInvariant:=function(Odisc, Linc)
      return 0;
    end;
    FuncIsomorphy:=function(Linc1, Linc2)
      local eCenter1, eCenter2, eIso, eVect1, eVect2, eTest;
      eCenter1:=Isobarycenter(EXT{Linc1});
      eCenter2:=Isobarycenter(EXT{Linc2});
      eIso:=Isobarycenter(EXT);
      eVect1:=(eCenter1+eIso)/2;
      eVect2:=(eCenter2+eIso)/2;
      eTest:=MyEquivalence(EXT, EXT, eVect1, eVect2);
      if eTest<>false then
        return true;
      fi;
      return false;
    end;
    FuncInvariantUpdate:=function(OdiscPrev, NbCall)
      return 0;
    end;
    OrderLincStabilizer:=function(Linc)
      local eVect, eCenter;
      eCenter:=Isobarycenter(EXT{Linc});
      eVect:=(eCenter+M6__Grp)/2;
      return M6__Order(eVect);
    end;
    return OrbitGroupFormalism(EXT, M6__Grp, Prefix, SavingTrigger,
        rec(FuncInvariant:=FuncInvariant,
            FuncIsomorphy:=FuncIsomorphy,
            GroupOrder:=M6__Order(M6__Grp),
            OrderLincStabilizer:=OrderLincStabilizer,
            FuncInvariantUpdate:=FuncInvariantUpdate));
  end;
  M6__BankKeyInformation:=function(EXT, GroupExt)
    local LNB, TheInv, eChar;
    eChar:=Isobarycenter(EXT);
    return rec(eChar:=eChar, TheInv:=0);
  end;
  M6__BankCompleteInformation:=function(EXT, GroupExt, ListObject)
    return rec(EXT:=EXT, Group:=GroupExt, ListObject:=ListObject);
  end;
  M6__BankGetVertexSet:=function(TheKey, TheComplete)
    return TheComplete.EXT;
  end;
  M6__BankGetGroup:=function(TheKey, TheComplete)
    return TheComplete.Group;
  end;
  M6__BankGetListObject:=function(TheComplete)
    return TheComplete.ListObject;
  end;
  M6__BankGetForIsom:=function(TheKey)
    return TheKey;
  end;
  return rec(
    Stabilizer:=M6__Stabilizer,
    LiftingOrbits:=M6__LiftingOrbits,
    GroupUnion:=M6__GroupUnion,
    ToPermGroup:=M6__PermGroupAction,
    Order:=M6__Order,
    IsSubgroup:=M6__IsSubgroup,
    GroupConjugacy:=M6__GroupConjugacy,
    TransformIncidenceList:=M6__TransformIncidenceList,
    OrbitGroupFormalism:=M6__OrbitGroupFormalism,
    BankKeyInformation:=M6__BankKeyInformation,
    BankCompleteInformation:=M6__BankCompleteInformation,
    BankGetVertexSet:=M6__BankGetVertexSet,
    BankGetForIsom:=M6__BankGetForIsom,
    BankGetGroup:=M6__BankGetGroup,
    BankGetListObject:=M6__BankGetListObject);
end;



GetGRAcell_direct:=function(TheGramMat, ListPoint, ListRelevant)
  local nbPoint, GRA, i, j, eDiff, pos, eRepr, ePt, eOcand, eStab, PermGRP, ListPermGens, eList, ePerm, eMatrGen, Opt, eOpt, OcandAdj, fPt, GRP, eDist, DistMat;
  nbPoint:=Length(ListPoint);
  DistMat:=NullMat(nbPoint, nbPoint);
  for ePt in [1..nbPoint]
  do
    for fPt in [ePt+1..nbPoint]
    do
      eDiff:=ListPoint[ePt] - ListPoint[fPt];
      eDist:=eDiff * TheGramMat * eDiff;
      DistMat[ePt][fPt]:=eDist;
      DistMat[fPt][ePt]:=eDist;
    od;
  od;
  PermGRP:=AutomorphismGroupColoredGraph(DistMat);
  GRA:=NullGraph(PermGRP, nbPoint);
  Opt:=Orbits(PermGRP, [1..nbPoint], OnPoints);
  for eOpt in Opt
  do
    ePt:=eOpt[1];
    eStab:=Stabilizer(PermGRP, ePt, OnPoints);
    OcandAdj:=Orbits(eStab, [1..nbPoint], OnPoints);
    for eOcand in OcandAdj
    do
      eRepr:=eOcand[1];
      eDiff:=ListPoint[ePt] - ListPoint[eRepr];
      if Position(ListRelevant, eDiff)<>fail then
        AddEdgeOrbit(GRA, [ePt, eRepr]);
        AddEdgeOrbit(GRA, [eRepr, ePt]);
      fi;
    od;
  od;
  return GRA;
end;
