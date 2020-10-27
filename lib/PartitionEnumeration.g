PARTITION_GetGroupOnBlocks:=function(n, ListSet, GRPvert)
  local ListGenIndep, eGen, eList, ePermIndep;
  ListGenIndep:=[];
  for eGen in GeneratorsOfGroup(GRPvert)
  do
    eList:=List(ListSet, x->Position(ListSet, OnSets(x, eGen)));
    ePermIndep:=PermList(eList);
    Add(ListGenIndep, ePermIndep);
  od;
  return Group(ListGenIndep);
end;


PARTITION_GetMatrixPair:=function(n, GRPvert)
  local ListPair, Opair, nbO, TheMat, iO, eO, ePair, i, j, nbOreal;
  ListPair:=Combinations([1..n], 2);
  Opair:=OrbitsDomain(GRPvert, ListPair, OnSets);
  TheMat:=NullMat(n, n);
  nbO:=Length(Opair);
  nbOreal:=Minimum(nbO, 100);
  for iO in [1..nbOreal]
  do
    eO:=Opair[iO];
    for ePair in eO
    do
      i:=ePair[1];
      j:=ePair[2];
      TheMat[i][j]:=iO;
      TheMat[j][i]:=iO;
    od;
  od;
  return rec(n:=n, TheMat:=TheMat, nbOreal:=nbOreal);
end;


PARTITION_Invariant:=function(RecMat, eList)
  local eDiff, siz, sizB, eVect1, eVect2, i, j, eVal, fVal, iO;
  eDiff:=Difference([1..RecMat.n], eList);
  siz:=Length(eList);
  eVect1:=ListWithIdenticalEntries(RecMat.nbOreal,0);
  for i in [1..siz-1]
  do
    for j in [i+1..siz]
    do
      eVal:=eList[i];
      fVal:=eList[j];
      iO:=RecMat.TheMat[eVal][fVal];
      if iO > 0 then
        eVect1[iO]:=eVect1[iO]+1;
      fi;
    od;
  od;
  eVect2:=ListWithIdenticalEntries(RecMat.nbOreal,0);
  sizB:=RecMat.n-siz;
  for i in [1..siz]
  do
    for j in [1..sizB]
    do
      eVal:=eList[i];
      fVal:=eDiff[j];
      iO:=RecMat.TheMat[eVal][fVal];
      if iO > 0 then
        eVect2[iO]:=eVect2[iO]+1;
      fi;
     od;
  od;
  return rec(eVect1:=eVect1, eVect2:=eVect2);
end;



PARTITION_EnumerateEquivariant_Raw:=function(n, ListSet, GRPvert)
  local GRPset, nbSet, TheMat, iSet, eSet, eVect, RecMatrix, TheOpt, ListSol, ListSetSol, O, ListRepr, TotVect, OneVect;
  GRPset:=PARTITION_GetGroupOnBlocks(n, ListSet, GRPvert);
  nbSet:=Length(ListSet);
  TheMat:=NullMat(nbSet, n);
  TotVect:=ListWithIdenticalEntries(n,0);
  for iSet in [1..nbSet]
  do
    eSet:=ListSet[iSet];
    OneVect:=ListWithIdenticalEntries(Length(eSet),1);
    TotVect{eSet}:=OneVect;
    TheMat[iSet]{eSet}:=OneVect;
  od;
  if Position(TotVect,0)<>fail then
    return [];
  fi;
  eVect:=ListWithIdenticalEntries(n,1);
  #
  RecMatrix:=rec(TheMat:=TheMat, eVect:=eVect);
  #
  TheOpt:="binary";
  ListSol:=FindIntegralsolutions_Libexact(RecMatrix, TheOpt);
  Print("|ListSol|=", Length(ListSol), "\n");
  ListSetSol:=List(ListSol, x->Filtered([1..nbSet], iIndep->x[iIndep]=1));
  O:=OrbitsDomain(GRPset, ListSetSol, OnSets);
  Print("|O|=", Length(O), "\n");
  ListRepr:=List(O, x->x[1]);
  return ListRepr;
end;


PARTITION_EnumerateEquivariant_NextGen:=function(n, ListSet, GRPvert, RecFunc)
  local GRPset, sizGRP, nbSet, testRespawn, testAddiSymm, Opt, ListOrbit, FuncInsert, eOpt, eRepr, eSet, eDiff, ListAllowedSets, iSet, fSet, eInt, fSetRed, eStab, nRed, ListOrbSma, eOrb, GRPvertTot, GRPsetTot, RecMat, eOrbSma, iOpt, nbOpt, ListIdxAllowed, ListOriginOrbit, ListOrbitMerge;
  GRPset:=PARTITION_GetGroupOnBlocks(n, ListSet, GRPvert);
  sizGRP:=Order(GRPvert);
  nbSet:=Length(ListSet);
  Print("n=", n, " nbSet=", nbSet, " sizGRP=", sizGRP, "\n");
  testRespawn:=RecFunc.FuncRespawn(n, nbSet, sizGRP);
  Print("testRespawn=", testRespawn, "\n");
  if testRespawn=false then
    return PARTITION_EnumerateEquivariant_Raw(n, ListSet, GRPvert);
  fi;
  testAddiSymm:=RecFunc.FuncAddiSymm(n, nbSet, sizGRP);
  Print("testAddiSymm=", testAddiSymm, "\n");
  if testAddiSymm then
    GRPvertTot:=SetFamilyGroup(n, ListSet);
    GRPsetTot:=PARTITION_GetGroupOnBlocks(n, ListSet, GRPvertTot);
  else
    GRPvertTot:=GRPvert;
    GRPsetTot:=GRPset;
  fi;
  Print("|GRPvert|=", Order(GRPvert), " |GRPset|=", Order(GRPset), " |GRPvertTot|=", Order(GRPvertTot), " |GRPsetTot|=", Order(GRPsetTot), "\n");
  if IsSubgroup(GRPvertTot, GRPvert)=false then
    Error("One group inclusion is violated");
  fi;
  Opt:=OrbitsDomain(GRPsetTot, [1..nbSet], OnPoints);
  nbOpt:=Length(Opt);
  Print("|Opt|=", nbOpt, "\n");
  RecMat:=PARTITION_GetMatrixPair(nbSet, GRPsetTot);
  Print("RecMat.nbOreal=", RecMat.nbOreal, "\n");
  ListOriginOrbit:=ListWithIdenticalEntries(nbSet,0);
  for iOpt in [1..nbOpt]
  do
    eOpt:=Opt[iOpt];
    ListOriginOrbit{eOpt}:=ListWithIdenticalEntries(Length(eOpt), iOpt);
  od;
  ListOrbitMerge:=[];
  for iOpt in [1..nbOpt]
  do
    ListOrbit:=[];
    FuncInsert:=function(eSol)
      local eInv, eRec, fRec, testIso;
      eInv:=PARTITION_Invariant(RecMat, eSol);
      for fRec in ListOrbit
      do
        if fRec.eInv=eInv then
          testIso:=RepresentativeAction(GRPsetTot, eSol, fRec.eSol, OnSets);
          if testIso<>fail then
            return;
          fi;
        fi;
      od;
      eRec:=rec(eInv:=eInv, eSol:=eSol);
      Add(ListOrbit, eRec);
      Add(ListOrbitMerge, eSol);
    end;
    Print("iOpt=", iOpt, " / ", nbOpt, "\n");
    eOpt:=Opt[iOpt];
    eRepr:=eOpt[1];
    eSet:=ListSet[eRepr];
    eDiff:=Difference([1..n], eSet);
    ListAllowedSets:=[];
    ListIdxAllowed:=[];
    for iSet in Difference([1..nbSet], [eRepr])
    do
      if ListOriginOrbit[iSet] >= iOpt then
        fSet:=ListSet[iSet];
        eInt:=Intersection(eSet, fSet);
        if Length(eInt)=0 then
          fSetRed:=List(fSet, x->Position(eDiff, x));
          Add(ListAllowedSets, fSetRed);
          Add(ListIdxAllowed, iSet);
        fi;
      fi;
    od;
    eStab:=SecondReduceGroupAction(Stabilizer(GRPvertTot, eSet, OnSets), eDiff);
    nRed:=n - Length(eSet);
    ListOrbSma:=PARTITION_EnumerateEquivariant_NextGen(nRed, ListAllowedSets, eStab, RecFunc);
    for eOrbSma in ListOrbSma
    do
      eOrb:=Union(Set(ListIdxAllowed{eOrbSma}), [eRepr]);
      FuncInsert(eOrb);
    od;
    Print("Now |ListOrbitMerge|=", Length(ListOrbitMerge), " |ListOrbit|=", Length(ListOrbit), "\n");
  od;
  Print("Now doing the RETURN\n");
  return GlobalLiftingOrbitsOnSets(ListOrbitMerge, GRPset, GRPsetTot);
end;

