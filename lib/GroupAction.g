PermutedStabilizer:=function(TheGRP, eVect)
  local TheStab, Hset, eVal, ListIdx;
  TheStab:=ShallowCopy(TheGRP);
  Hset:=Set(eVect);
  for eVal in Hset
  do
    ListIdx:=Filtered([1..Length(eVect)], x->eVect[x]=eVal);
    TheStab:=Stabilizer(TheStab, ListIdx, OnSets);
  od;
  return TheStab;
end;

PermutedRepresentativeAction:=function(TheGRP, eVect1, eVect2)
  local TheStab, eVect1img, n, eSet1, eSet2, g, eVal, ListIdx1, ListIdx2, gT;
  eVect1img:=ShallowCopy(eVect1);
  n:=Length(eVect1);
  eSet1:=Set(eVect1);
  eSet2:=Set(eVect2);
  if eSet1<>eSet2 then
    return fail;
  fi;
  g:=();
  TheStab:=ShallowCopy(TheGRP);
  for eVal in eSet1
  do
    ListIdx1:=Filtered([1..n], x->eVect1img[x]=eVal);
    ListIdx2:=Filtered([1..n], x->eVect2[x]=eVal);
    gT:=RepresentativeAction(TheStab, ListIdx1, ListIdx2, OnSets);
    if gT=fail then
      return fail;
    fi;
    eVect1img:=Permuted(eVect1img, gT);
    g:=g*gT;
    if eVect1img=eVect2 then
      return g;
    fi;
    TheStab:=Stabilizer(TheStab, ListIdx2, OnSets);
  od;
end;



OnTuplesRepresentativeAction:=function(SymGrp, Tuple1, Tuple2)
  local Tuple1Second, GrpStab, eEltSearch, i, eGen;
  if Length(Tuple1)<>Length(Tuple2) then
    return fail;
  fi;
  Tuple1Second:=ShallowCopy(Tuple1);
  GrpStab:=ShallowCopy(SymGrp);
  eEltSearch:=();
  for i in [1..Length(Tuple1)]
  do
    eGen:=RepresentativeAction(GrpStab, Tuple1Second[i], Tuple2[i], OnPoints);
    if eGen=fail then
      return fail;
    fi;
    eEltSearch:=eEltSearch*eGen;
    Tuple1Second:=OnTuples(Tuple1Second, eGen);
    if Tuple1Second=Tuple2 then
      return eEltSearch;
    fi;
    GrpStab:=Stabilizer(GrpStab, Tuple1Second[i], OnPoints);
    GrpStab:=Group(SmallGeneratingSet(GrpStab));
  od;
end;

OnTuplesStabilizer:=function(GRP, eTuple)
  local ReturnedStab, ePoint;
  ReturnedStab:=Group(GeneratorsOfGroup(GRP));
  for ePoint in eTuple
  do
    ReturnedStab:=Stabilizer(ReturnedStab, ePoint, OnPoints);
  od;
  return ReturnedStab;
end;






OnTuplesCanonicalization:=function(GroupEXT, ListPts)
  local g, ReturnedTuple, GrpStab, iRank, TheMin;
  ReturnedTuple:=ShallowCopy(ListPts);
  GrpStab:=ShallowCopy(GroupEXT);
  for iRank in [1..Length(ListPts)]
  do
    TheMin:=Minimum(Orbit(GrpStab, ReturnedTuple[iRank], OnPoints));
    g:=RepresentativeAction(GrpStab, ReturnedTuple[iRank], TheMin, OnPoints);
    ReturnedTuple:=OnTuples(ReturnedTuple, g);
    GrpStab:=Stabilizer(GrpStab, ReturnedTuple[iRank], OnPoints);
  od;
  return ReturnedTuple;
end;

OnTuplesSetsStabilizer:=function(GRP, eTuple)
  local ReturnedStab, ListLen, ePerm, eTupleReord, eSet;
  ReturnedStab:=Group(GeneratorsOfGroup(GRP));
  ListLen:=List(eTuple, Length);
  ePerm:=SortingPerm(ListLen);
  eTupleReord:=Permuted(eTuple, ePerm);
  for eSet in eTupleReord
  do
#    Print("|eSet|=", Length(eSet), "\n");
    ReturnedStab:=Stabilizer(ReturnedStab, eSet, OnSets);
#    Print("|ReturnedStab|=", Order(ReturnedStab), "\n");
  od;
  return ReturnedStab;
end;



OnTuplesSetsRepresentativeAction:=function(GroupEXT, FlagEXT1, FlagEXT2)
  local GroupElement, FlagPrev1, GrpStab, iRank, g;
  GroupElement:=();
  FlagPrev1:=ShallowCopy(FlagEXT1);
  GrpStab:=ShallowCopy(GroupEXT);
  for iRank in [1..Length(FlagEXT1)]
  do
    g:=RepresentativeAction(GrpStab, FlagPrev1[iRank], FlagEXT2[iRank], OnSets);
    if g=fail then
      return fail;
    fi;
    FlagPrev1:=OnTuplesSets(FlagPrev1, g);
    GrpStab:=Stabilizer(GrpStab, FlagPrev1[iRank], OnSets);
    GroupElement:=GroupElement*g;
  od;
  return GroupElement;
end;

OnTuplesSetsCanonicalization:=function(GroupEXT, ListSet)
  local g, ReturnedTuple, GrpStab, iRank, TheMin;
  ReturnedTuple:=ShallowCopy(ListSet);
  GrpStab:=ShallowCopy(GroupEXT);
  for iRank in [1..Length(ListSet)]
  do
    TheMin:=Minimum(Orbit(GrpStab, ReturnedTuple[iRank], OnSets));
    g:=RepresentativeAction(GrpStab, ReturnedTuple[iRank], TheMin, OnSets);
    ReturnedTuple:=OnTuplesSets(ReturnedTuple, g);
    GrpStab:=Stabilizer(GrpStab, ReturnedTuple[iRank], OnSets);
  od;
  return ReturnedTuple;
end;







OnSetsSetsRepresentativeAction:=function(GRP, eSetSet1, eSetSet2)
  local InitialCase, nbSet, WorkingCase, NextInTree, GoUpNextInTree, result;
  if Length(eSetSet1)<>Length(eSetSet2) then
    return fail;
  fi;
  nbSet:=Length(eSetSet1);
  WorkingCase:=rec(len:=0,
                   ListAssignment:=ListWithIdenticalEntries(nbSet, 0), 
                   ListIndices:=ListWithIdenticalEntries(nbSet, 0), 
                   ListCases:=[rec(g:=(), TheGrp:=Group(GeneratorsOfGroup(GRP)))]);
  NextInTree:=function()
    local len, nbCase, eTrySet, TheDiff, idx, gRel, GRPrel, eSet2, h, RedGrp;
    len:=WorkingCase.len;
    nbCase:=len+1;
    eTrySet:=eSetSet1[nbCase];
    TheDiff:=Difference([1..nbSet], Set(WorkingCase.ListAssignment{[1..len]}));
    gRel:=WorkingCase.ListCases[nbCase].g;
    GRPrel:=WorkingCase.ListCases[nbCase].TheGrp;
    idx:=1;
    while(true)
    do
      eSet2:=OnSets(eTrySet, gRel);
      h:=RepresentativeAction(GRPrel, eSet2, eSetSet2[TheDiff[idx]], OnSets);
      if h<>fail then
        RedGrp:=Stabilizer(GRPrel, eSetSet2[TheDiff[idx]], OnSets);
        WorkingCase.ListCases[nbCase+1]:=rec(g:=gRel*h, TheGrp:=RedGrp);
        WorkingCase.len:=nbCase;
        WorkingCase.ListAssignment[nbCase]:=TheDiff[idx];
        WorkingCase.ListIndices[nbCase]:=idx;
        if nbCase=nbSet then
          return gRel*h;
        else
          return "unfinished";
        fi;
      fi;
      if idx=Length(TheDiff) then
        break;
      fi;
      idx:=idx+1;
    od;
    return GoUpNextInTree();
  end;
  GoUpNextInTree:=function()
    local len, nbCase, idx, TheDiff, eTrySet, gRel, GRPrel, eSet2, h, RedGrp;
    while(true)
    do
      if WorkingCase.len=0 then
        return fail;
      fi;
      len:=WorkingCase.len;
      nbCase:=len+1;
      idx:=WorkingCase.ListIndices[nbCase-1];
      TheDiff:=Difference([1..nbSet], Set(WorkingCase.ListAssignment{[1..len-1]}));
      eTrySet:=eSetSet1[len];
      gRel:=WorkingCase.ListCases[nbCase-1].g;
      GRPrel:=WorkingCase.ListCases[nbCase-1].TheGrp;
      while(true)
      do
        if idx=Length(TheDiff) then
          break;
        fi;
        idx:=idx+1;
        eSet2:=OnSets(eTrySet, gRel);
        h:=RepresentativeAction(GRPrel, eSet2, eSetSet2[TheDiff[idx]], OnSets);
        if h<>fail then
          RedGrp:=Stabilizer(GRPrel, eSetSet2[TheDiff[idx]], OnSets);
          WorkingCase.ListCases[nbCase]:=rec(g:=gRel*h, TheGrp:=RedGrp);
          WorkingCase.ListAssignment[nbCase-1]:=TheDiff[idx];
          WorkingCase.ListIndices[nbCase-1]:=idx;
          if nbCase=nbSet+1 then
            return gRel*h;
          else
            return "unfinished";
          fi;
        fi;
      od;
      WorkingCase.len:=len-1;
      Unbind(WorkingCase.ListCases[nbCase]);
      WorkingCase.ListAssignment[len]:=0;
      WorkingCase.ListIndices[len]:=0;
    od;
  end;
  while(true)
  do
    result:=NextInTree();
    if result=fail then
      return fail;
    fi;
    if result<>"unfinished" then
      if OnSetsSets(eSetSet1, result)<>eSetSet2 then
        Error("We have inconsistency in OnSetsSetsRepr..");
      fi;
      return result;
    fi;
  od;
end;




OnSetsSetsStabilizer:=function(GRP, eSetSet)
  local ListGens, eStab, GetGroupOnListSets, SoughtGroup, SetInducedGroup, NextInTree, GoUpNextInTree, FuncInsertSolvedCase, IsItASolvedCase, FuncInsertGenerators, nbSet, O, WorkingCase, result, ListSolvedCases, eGen;
  ListGens:=[];
  eStab:=Stabilizer(GRP, eSetSet, OnTuplesSets);
  GetGroupOnListSets:=function(ListGen)
    local NewListGens, eGen, eList;
    NewListGens:=[];
    for eGen in ListGen
    do
      eList:=List(eSetSet, x->Position(eSetSet, OnSets(x, eGen)));
      Add(NewListGens, PermList(eList));
    od;
    return PersoGroupPerm(NewListGens);
  end;
  Append(ListGens, GeneratorsOfGroup(eStab));
  SoughtGroup:=PersoGroupPerm(ListGens);
  SetInducedGroup:=GetGroupOnListSets(ListGens);
  ListSolvedCases:=[];
  FuncInsertSolvedCase:=function(eCase)
    local ListKept, iCase, fCase, iStatus, fSetRed, eRepr;
    ListKept:=[];
    for iCase in [1..Length(ListSolvedCases)]
    do
      fCase:=ListSolvedCases[iCase];
      iStatus:=1;
      if fCase.len>=eCase.len then
        fSetRed:=fCase.eList{[1..eCase.len]};
        eRepr:=RepresentativeAction(SetInducedGroup, fSetRed, eCase.eList, OnTuples);
        if eRepr<>false then
          iStatus:=0;
        fi;
      fi;
      if iStatus=1 then
        Add(ListKept, iCase);
      fi;
    od;
    ListSolvedCases:=Concatenation(ListSolvedCases{ListKept}, [eCase]);    
  end;
  IsItASolvedCase:=function(eCase)
    local fCase, fSetRed, eRepr;
    for fCase in ListSolvedCases
    do
      if fCase.len>=eCase.len then
        fSetRed:=fCase.eList{[1..eCase.len]};
        eRepr:=RepresentativeAction(SetInducedGroup, fSetRed, eCase.eList, OnTuples);
        if eRepr<>false then
          return true;
        fi;
      fi;
    od;
    return false;
  end;
  FuncInsertGenerators:=function(eGen)
    if not(eGen in SoughtGroup) then
      Add(ListGens, eGen);
      SoughtGroup:=Group(ListGens);
      SetInducedGroup:=GetGroupOnListSets(ListGens);
    fi;
  end;
  nbSet:=Length(eSetSet);
  WorkingCase:=rec(len:=0,
                   ListAssignment:=ListWithIdenticalEntries(nbSet, 0), 
                   ListIndices:=ListWithIdenticalEntries(nbSet, 0), 
                   ListCases:=[rec(g:=(), TheGrp:=Group(GeneratorsOfGroup(GRP)))]);
  NextInTree:=function()
    local len, nbCase, eTrySet, TheDiff, idx, gRel, GRPrel, eSet2, h, RedGrp, eCase;
    len:=WorkingCase.len;
    if len=nbSet then
      return GoUpNextInTree();
    fi;
    nbCase:=len+1;
    eCase:=rec(len:=WorkingCase.len, eList:=WorkingCase.ListAssignment{[1..len]});
    if IsItASolvedCase(eCase)=true then
      return GoUpNextInTree();
    fi;
    eTrySet:=eSetSet[nbCase];
    TheDiff:=Difference([1..nbSet], Set(WorkingCase.ListAssignment{[1..len]}));
    gRel:=WorkingCase.ListCases[nbCase].g;
    GRPrel:=WorkingCase.ListCases[nbCase].TheGrp;
    idx:=1;
    while(true)
    do
      eSet2:=OnSets(eTrySet, gRel);
      h:=RepresentativeAction(GRPrel, eSet2, eSetSet[TheDiff[idx]], OnSets);
      if h<>fail then
        RedGrp:=Stabilizer(GRPrel, eSetSet[TheDiff[idx]], OnSets);
        WorkingCase.ListCases[nbCase+1]:=rec(g:=gRel*h, TheGrp:=RedGrp);
        WorkingCase.len:=nbCase;
        WorkingCase.ListAssignment[nbCase]:=TheDiff[idx];
        WorkingCase.ListIndices[nbCase]:=idx;
        if nbCase=nbSet then
          return gRel*h;
        else
          return "unfinished";
        fi;
      fi;
      if idx=Length(TheDiff) then
        break;
      fi;
      idx:=idx+1;
    od;
    return GoUpNextInTree();
  end;
  GoUpNextInTree:=function()
    local len, nbCase, idx, TheDiff, eTrySet, gRel, GRPrel, eSet2, h, RedGrp;
    while(true)
    do
      if WorkingCase.len=0 then
        return fail;
      fi;
      len:=WorkingCase.len;
      nbCase:=len+1;
      idx:=WorkingCase.ListIndices[nbCase-1];
      TheDiff:=Difference([1..nbSet], Set(WorkingCase.ListAssignment{[1..len-1]}));
      eTrySet:=eSetSet[len];
      gRel:=WorkingCase.ListCases[nbCase-1].g;
      GRPrel:=WorkingCase.ListCases[nbCase-1].TheGrp;
      while(true)
      do
        if idx=Length(TheDiff) then
          break;
        fi;
        idx:=idx+1;
        eSet2:=OnSets(eTrySet, gRel);
        h:=RepresentativeAction(GRPrel, eSet2, eSetSet[TheDiff[idx]], OnSets);
        if h<>fail then
          RedGrp:=Stabilizer(GRPrel, eSetSet[TheDiff[idx]], OnSets);
          WorkingCase.ListCases[nbCase]:=rec(g:=gRel*h, TheGrp:=RedGrp);
          WorkingCase.ListAssignment[nbCase-1]:=TheDiff[idx];
          WorkingCase.ListIndices[nbCase-1]:=idx;
          if nbCase=nbSet+1 then
            return gRel*h;
          else
            return "unfinished";
          fi;
        fi;
      od;
      WorkingCase.len:=len-1;
      Unbind(WorkingCase.ListCases[nbCase]);
      WorkingCase.ListAssignment[len]:=0;
      WorkingCase.ListIndices[len]:=0;
    od;
  end;
  while(true)
  do
    result:=NextInTree();
    if result=fail then
      break;
    fi;
    if result<>"unfinished" then
      FuncInsertGenerators(result);
    fi;
  od;
  for eGen in GeneratorsOfGroup(SoughtGroup)
  do
    if OnSetsSets(eSetSet, eGen)<>eSetSet then
      Error("We have inconsistency here, please check");
    fi;
  od;
  return SoughtGroup;
end;



OnSetsListSets:=function(eSetListSet, g)
  return Set(List(eSetListSet, x->OnTuplesSets(x,g)));
end;


OnSetsListSetsRepresentativeAction:=function(GRP, eSetListSet1, eSetListSet2)
  local InitialCase, nbSet, WorkingCase, NextInTree, GoUpNextInTree, result;
  if Length(eSetListSet1)<>Length(eSetListSet2) then
    return fail;
  fi;
  nbSet:=Length(eSetListSet1);
  WorkingCase:=rec(len:=0,
                   ListAssignment:=ListWithIdenticalEntries(nbSet, 0), 
                   ListIndices:=ListWithIdenticalEntries(nbSet, 0), 
                   ListCases:=[rec(g:=(), TheGrp:=Group(GeneratorsOfGroup(GRP)))]);
  NextInTree:=function()
    local len, nbCase, eTrySet, TheDiff, idx, gRel, GRPrel, eSet2, h, RedGrp;
    len:=WorkingCase.len;
    nbCase:=len+1;
    eTrySet:=eSetListSet1[nbCase];
    TheDiff:=Difference([1..nbSet], Set(WorkingCase.ListAssignment{[1..len]}));
    gRel:=WorkingCase.ListCases[nbCase].g;
    GRPrel:=WorkingCase.ListCases[nbCase].TheGrp;
    idx:=1;
    while(true)
    do
      eSet2:=OnTuplesSets(eTrySet, gRel);
      h:=OnTuplesSetsRepresentativeAction(GRPrel, eSet2, eSetListSet2[TheDiff[idx]]);
      if h<>fail then
        RedGrp:=OnTuplesSetsStabilizer(GRPrel, eSetListSet2[TheDiff[idx]]);
        WorkingCase.ListCases[nbCase+1]:=rec(g:=gRel*h, TheGrp:=RedGrp);
        WorkingCase.len:=nbCase;
        WorkingCase.ListAssignment[nbCase]:=TheDiff[idx];
        WorkingCase.ListIndices[nbCase]:=idx;
        if nbCase=nbSet then
          return gRel*h;
        else
          return "unfinished";
        fi;
      fi;
      if idx=Length(TheDiff) then
        break;
      fi;
      idx:=idx+1;
    od;
    return GoUpNextInTree();
  end;
  GoUpNextInTree:=function()
    local len, nbCase, idx, TheDiff, eTrySet, gRel, GRPrel, eSet2, h, RedGrp;
    while(true)
    do
      if WorkingCase.len=0 then
        return fail;
      fi;
      len:=WorkingCase.len;
      nbCase:=len+1;
      idx:=WorkingCase.ListIndices[nbCase-1];
      TheDiff:=Difference([1..nbSet], Set(WorkingCase.ListAssignment{[1..len-1]}));
      eTrySet:=eSetListSet1[len];
      gRel:=WorkingCase.ListCases[nbCase-1].g;
      GRPrel:=WorkingCase.ListCases[nbCase-1].TheGrp;
      while(true)
      do
        if idx=Length(TheDiff) then
          break;
        fi;
        idx:=idx+1;
        eSet2:=OnTuplesSets(eTrySet, gRel);
        h:=OnTuplesSetsRepresentativeAction(GRPrel, eSet2, eSetListSet2[TheDiff[idx]]);
        if h<>fail then
          RedGrp:=OnTuplesSetsStabilizer(GRPrel, eSetListSet2[TheDiff[idx]]);
          WorkingCase.ListCases[nbCase]:=rec(g:=gRel*h, TheGrp:=RedGrp);
          WorkingCase.ListAssignment[nbCase-1]:=TheDiff[idx];
          WorkingCase.ListIndices[nbCase-1]:=idx;
          if nbCase=nbSet+1 then
            return gRel*h;
          else
            return "unfinished";
          fi;
        fi;
      od;
      WorkingCase.len:=len-1;
      Unbind(WorkingCase.ListCases[nbCase]);
      WorkingCase.ListAssignment[len]:=0;
      WorkingCase.ListIndices[len]:=0;
    od;
  end;
  while(true)
  do
    result:=NextInTree();
    if result=fail then
      return fail;
    fi;
    if result<>"unfinished" then
      if OnSetsListSets(eSetListSet1, result)<>eSetListSet2 then
        Error("We have inconsistency in OnSetsListSetsRepr..");
      fi;
      return result;
    fi;
  od;
end;




OnSetsListSetsStabilizer:=function(GRP, eSetListSet)
  local ListGens, eStab, GetGroupOnListSets, SoughtGroup, SetInducedGroup, NextInTree, GoUpNextInTree, FuncInsertSolvedCase, IsItASolvedCase, FuncInsertGenerators, nbSet, O, WorkingCase, result, ListSolvedCases, eGen;
  ListGens:=[];
  eStab:=Stabilizer(GRP, eSetListSet, OnTuplesSets);
  GetGroupOnListSets:=function(ListGen)
    local NewListGens, eGen, eList;
    NewListGens:=[];
    for eGen in ListGen
    do
      eList:=List(eSetListSet, x->Position(eSetListSet, OnTuplesSets(x, eGen)));
      Add(NewListGens, PermList(eList));
    od;
    return PersoGroupPerm(NewListGens);
  end;
  Append(ListGens, GeneratorsOfGroup(eStab));
  SoughtGroup:=PersoGroupPerm(ListGens);
  SetInducedGroup:=GetGroupOnListSets(ListGens);
  ListSolvedCases:=[];
  FuncInsertSolvedCase:=function(eCase)
    local ListKept, iCase, fCase, iStatus, fSetRed, eRepr;
    ListKept:=[];
    for iCase in [1..Length(ListSolvedCases)]
    do
      fCase:=ListSolvedCases[iCase];
      iStatus:=1;
      if fCase.len>=eCase.len then
        fSetRed:=fCase.eList{[1..eCase.len]};
        eRepr:=RepresentativeAction(SetInducedGroup, fSetRed, eCase.eList, OnTuples);
        if eRepr<>false then
          iStatus:=0;
        fi;
      fi;
      if iStatus=1 then
        Add(ListKept, iCase);
      fi;
    od;
    ListSolvedCases:=Concatenation(ListSolvedCases{ListKept}, [eCase]);    
  end;
  IsItASolvedCase:=function(eCase)
    local fCase, fSetRed, eRepr;
    for fCase in ListSolvedCases
    do
      if fCase.len>=eCase.len then
        fSetRed:=fCase.eList{[1..eCase.len]};
        eRepr:=RepresentativeAction(SetInducedGroup, fSetRed, eCase.eList, OnTuples);
        if eRepr<>false then
          return true;
        fi;
      fi;
    od;
    return false;
  end;
  FuncInsertGenerators:=function(eGen)
    if not(eGen in SoughtGroup) then
      Add(ListGens, eGen);
      SoughtGroup:=Group(ListGens);
      SetInducedGroup:=GetGroupOnListSets(ListGens);
    fi;
  end;
  nbSet:=Length(eSetListSet);
  WorkingCase:=rec(len:=0,
ListAssignment:=ListWithIdenticalEntries(nbSet, 0), 
ListIndices:=ListWithIdenticalEntries(nbSet, 0), 
ListCases:=[rec(g:=(), TheGrp:=Group(GeneratorsOfGroup(GRP)))]);
  NextInTree:=function()
    local len, nbCase, eTrySet, TheDiff, idx, gRel, GRPrel, eSet2, h, RedGrp, eCase;
    len:=WorkingCase.len;
    if len=nbSet then
      return GoUpNextInTree();
    fi;
    nbCase:=len+1;
    eCase:=rec(len:=WorkingCase.len, eList:=WorkingCase.ListAssignment{[1..len]});
    if IsItASolvedCase(eCase)=true then
      return GoUpNextInTree();
    fi;
    eTrySet:=eSetListSet[nbCase];
    TheDiff:=Difference([1..nbSet], Set(WorkingCase.ListAssignment{[1..len]}));
    gRel:=WorkingCase.ListCases[nbCase].g;
    GRPrel:=WorkingCase.ListCases[nbCase].TheGrp;
    idx:=1;
    while(true)
    do
      eSet2:=OnTuplesSets(eTrySet, gRel);
      h:=OnTuplesSetsRepresentativeAction(GRPrel, eSet2, eSetListSet[TheDiff[idx]]);
      if h<>fail then
        RedGrp:=OnTuplesSetsStabilizer(GRPrel, eSetListSet[TheDiff[idx]]);
        WorkingCase.ListCases[nbCase+1]:=rec(g:=gRel*h, TheGrp:=RedGrp);
        WorkingCase.len:=nbCase;
        WorkingCase.ListAssignment[nbCase]:=TheDiff[idx];
        WorkingCase.ListIndices[nbCase]:=idx;
        if nbCase=nbSet then
          return gRel*h;
        else
          return "unfinished";
        fi;
      fi;
      if idx=Length(TheDiff) then
        break;
      fi;
      idx:=idx+1;
    od;
    return GoUpNextInTree();
  end;
  GoUpNextInTree:=function()
    local len, nbCase, idx, TheDiff, eTrySet, gRel, GRPrel, eSet2, h, RedGrp;
    while(true)
    do
      if WorkingCase.len=0 then
        return fail;
      fi;
      len:=WorkingCase.len;
      nbCase:=len+1;
      idx:=WorkingCase.ListIndices[nbCase-1];
      TheDiff:=Difference([1..nbSet], Set(WorkingCase.ListAssignment{[1..len-1]}));
      eTrySet:=eSetListSet[len];
      gRel:=WorkingCase.ListCases[nbCase-1].g;
      GRPrel:=WorkingCase.ListCases[nbCase-1].TheGrp;
      while(true)
      do
        if idx=Length(TheDiff) then
          break;
        fi;
        idx:=idx+1;
        eSet2:=OnTuplesSets(eTrySet, gRel);
        h:=OnTuplesSetsRepresentativeAction(GRPrel, eSet2, eSetListSet[TheDiff[idx]]);
        if h<>fail then
          RedGrp:=OnTuplesSetsStabilizer(GRPrel, eSetListSet[TheDiff[idx]]);
          WorkingCase.ListCases[nbCase]:=rec(g:=gRel*h, TheGrp:=RedGrp);
          WorkingCase.ListAssignment[nbCase-1]:=TheDiff[idx];
          WorkingCase.ListIndices[nbCase-1]:=idx;
          if nbCase=nbSet+1 then
            return gRel*h;
          else
            return "unfinished";
          fi;
        fi;
      od;
      WorkingCase.len:=len-1;
      Unbind(WorkingCase.ListCases[nbCase]);
      WorkingCase.ListAssignment[len]:=0;
      WorkingCase.ListIndices[len]:=0;
    od;
  end;
  while(true)
  do
    result:=NextInTree();
    if result=fail then
      break;
    fi;
    if result<>"unfinished" then
      FuncInsertGenerators(result);
    fi;
  od;
  for eGen in GeneratorsOfGroup(SoughtGroup)
  do
    if OnSetsListSets(eSetListSet, eGen)<>eSetListSet then
      Error("We have inconsistency here");
    fi;
  od;
  return SoughtGroup;
end;



OrbitsSafe:=function(GRP, ListPt, TheAction)
  local nbPt, ListStatus, ListRepr, ListLen, pos, ePtRepr, eOrb, ePt, posB;
  nbPt:=Length(ListPt);
  ListStatus:=ListWithIdenticalEntries(nbPt, 1);
  ListRepr:=[];
  ListLen:=[];
  while(true)
  do
    pos:=Position(ListStatus,1);
    if pos=fail then
      break;
    fi;
    ePtRepr:=ListPt[pos];
    Add(ListRepr, ePtRepr);
    eOrb:=Orbit(GRP, ePtRepr, TheAction);
    Add(ListLen, Length(eOrb));
    for ePt in eOrb
    do
      posB:=Position(ListPt, ePt);
      if posB=fail then
        Error("point does not belong to ListPt");
      fi;
      if ListStatus[posB]=0 then
        Error("The point is already assigned");
      fi;
      ListStatus[posB]:=0;
    od;
  od;
  return rec(ListRepr:=ListRepr, ListLen:=ListLen);
end;







OrbitWithAction:=function(TheGRP, ThePoint, TheAction)
  local ListCoset, ListStatus, ListElement, IsFinished, eGen, nbCos, iCos, fCos;
  ListCoset:=[ThePoint];
  ListStatus:=[1];
  ListElement:=[Identity(TheGRP)];
  while(true)
  do
    IsFinished:=true;
    nbCos:=Length(ListCoset);
    for iCos in [1..nbCos]
    do
      if ListStatus[iCos]=1 then
        ListStatus[iCos]:=0;
        IsFinished:=false;
        for eGen in GeneratorsOfGroup(TheGRP)
        do
          fCos:=TheAction(ListCoset[iCos], eGen);
          if Position(ListCoset, fCos)=fail then
            Add(ListCoset, fCos);
            Add(ListStatus, 1);
            Add(ListElement, ListElement[iCos]*eGen);
          fi;
        od;
      fi;
    od;
    if IsFinished=true then
      break;
    fi;
  od;
  return rec(ListCoset:=ListCoset, ListElement:=ListElement);
end;


# this is the right cosets that are enumerated.
GetCosetsBySplittingFunction:=function(TheGRP, TheSplitFct)
  local ListCoset, ListStatus, IsFinished, eGen, nbCos, iCos, fCos, GetPosition, pos, eElt, ListGeneratorSubgroup;
  ListCoset:=[Identity(TheGRP)];
  ListGeneratorSubgroup:=[];
  ListStatus:=[1];
  GetPosition:=function(eElt)
    local iCos, InvElt, eProd;
    InvElt:=Inverse(eElt);
    for iCos in [1..Length(ListCoset)]
    do
      eProd:=ListCoset[iCos]*InvElt;
      if TheSplitFct(eProd)=true then
        Add(ListGeneratorSubgroup, eProd);
        return iCos;
      fi;
    od;
    return fail;
  end;
  while(true)
  do
    IsFinished:=true;
    nbCos:=Length(ListCoset);
    for iCos in [1..nbCos]
    do
      if ListStatus[iCos]=1 then
        ListStatus[iCos]:=0;
        IsFinished:=false;
        for eGen in GeneratorsOfGroup(TheGRP)
        do
          eElt:=ListCoset[iCos]*eGen;
          pos:=GetPosition(eElt);
          if pos=fail then
            Add(ListCoset, eElt);
            Add(ListStatus, 1);
          fi;
        od;
      fi;
    od;
    if IsFinished=true then
      break;
    fi;
  od;
  return rec(ListCoset:=ListCoset, ListGeneratorSubgroup:=ListGeneratorSubgroup);
end;

GetKernelOfMapping:=function(GRP1, GRP2, ListGens1, ListGens2)
  local phi, TheId1, TheId2, NewListGens, TheSubgroup, FuncInsert, eElt;
  phi:=GroupHomomorphismByImagesNC(GRP1, GRP2, ListGens1, ListGens2);
  TheId1:=Identity(GRP1);
  TheId2:=Identity(GRP2);
  NewListGens:=[];
  TheSubgroup:=Group([TheId1]);
  FuncInsert:=function(eElt)
    if Image(phi, eElt)=TheId2 then
      if eElt in TheSubgroup then
        return;
      fi;
      Add(NewListGens, eElt);
      TheSubgroup:=Group(NewListGens);
    fi;
  end;
  for eElt in GRP1
  do
    FuncInsert(eElt);
  od;
  return TheSubgroup;
end;

GetIndexOneTwoKernelOfMapping:=function(GRP1, GRP2, ListGens1, ListGens2)
  local nbGen, ListPosPlus, ListPosMinus, ListGenRet, x1, TheId, eGenMinus, eGenPlus, List1, List2, i1, i2;
  if First(ListGens2, x->x<>() and x<>(1,2))<>fail then
    Error("The ListGens2 must be only () or (1,2)");
  fi;
  if GRP2<>SymmetricGroup(2) then
    Error("The second group must be SymmetricGroup(2)");
  fi;
  nbGen:=Length(ListGens2);
  ListPosPlus:=Filtered([1..nbGen], x->ListGens2[x]=());
  ListPosMinus:=Filtered([1..nbGen], x->ListGens2[x]=(1,2));
  if Length(ListPosMinus)=0 then
    return GRP1;
  fi;
  ListGenRet:=ListGens1{ListPosPlus};
  x1:=ListGens1[ListPosMinus[1]];
  TheId:=Identity(GRP1);
  for eGenMinus in ListGens1{ListPosMinus}
  do
    for eGenPlus in Concatenation(ListPosPlus, TheId)
    do
      List1:=[eGenMinus, Inverse(eGenMinus)];
      List2:=[x1, Inverse(x1)];
      for i1 in [1,2]
      do
        for i2 in [1,2]
        do
          Add(ListGenRet, List1[i1]*eGenPlus*List2[i2]);
          Add(ListGenRet, List2[i2]*eGenPlus*List1[i1]);
        od;
      od;
    od;
  od;
  return Group(ListGenRet);
end;







MatrixGroupPermutationRepresentation:=function(GRP1, GRP2, nbPoint, ListGens1, ListGens2)
  local phi, GetKernel_meth1, TheKer, GetPreImage, GetStabilizerPoint_meth1, GetKernel_meth2, GetStabilizerPoint_meth2;
  phi:=GroupHomomorphismByImagesNC(GRP1, GRP2, ListGens1, ListGens2);
  GetKernel_meth1:=function()
    local ListGen, TheKer;
    ListGen:=CoKernelGensPermHom(InverseGeneralMapping(phi));
    TheKer:=Group(ListGen);
    return TheKer;
  end;
  GetKernel_meth2:=function()
    return Stabilizer(GRP1, [1..nbPoint], ListGens1, ListGens2, OnTuples);
  end;
  # An alternative method is provided by an e-mail of Alexander Hulpke
  TheKer:=GetKernel_meth1();
#  TheKer:=GetKernel_meth2();
  GetPreImage:=function(ePerm)
    return PreImagesRepresentative(phi, ePerm);
  end;
  GetStabilizerPoint_meth1:=function(ePt)
    local GRPstab, ListGens1, ListGens2, ListGen;
    GRPstab:=Stabilizer(GRP2, ePt, OnPoints);
    ListGens1:=List(GeneratorsOfGroup(GRPstab), GetPreImage);
    ListGens2:=GeneratorsOfGroup(TheKer);
    ListGen:=Concatenation(ListGens1, ListGens2);
    Print("|TheKer|=", Order(TheKer), "\n");
    return Group(ListGen);
  end;
  GetStabilizerPoint_meth2:=function(ePt)
    return Stabilizer(GRP1, ePt, ListGens1, ListGens2, OnPoints);
  end;
  return rec(TheKer:=TheKer, 
             GetStabilizerPoint:=GetStabilizerPoint_meth2);
end;




GetRotationSubgroup:=function(GRP, FctSign)
  local ListMatrGens, ListSignGens, eGen, eDet, GRPsym;
  ListMatrGens:=GeneratorsOfGroup(GRP);
  ListSignGens:=[];
  for eGen in ListMatrGens
  do
    eDet:=FctSign(eGen);
    if eDet=-1 then
      Add(ListSignGens, (1,2));
    else
      Add(ListSignGens, ());
    fi;
  od;
  GRPsym:=Group([(1,2)]);
  return GetKernelOfMapping(GRP, GRPsym, ListMatrGens, ListSignGens);
end;

LinearSpace_GetDivisor:=function(TheSpace)
  local n, TheDet, eDiv, eMat, IsOK, eVect, eSol;
  n:=Length(TheSpace);
  TheDet:=AbsInt(DeterminantMat(TheSpace));
  eDiv:=1;
  while(true)
  do
    eMat:=eDiv*IdentityMat(n);
    IsOK:=true;
    for eVect in eMat
    do
      eSol:=SolutionIntMat(TheSpace, eVect);
      if eSol=fail then
        IsOK:=false;
      fi;
    od;
    if IsOK=true then
      return eDiv;
    fi;
#    Print("eDiv=", eDiv, "\n");
   eDiv:=eDiv+1;
  od;
  Error("We should never reach that stage");
end;


LinearSpace_ModStabilizer:=function(GRPmatr, TheSpace, TheMod)
  local n, TheSpaceMod, TheAction, IsStabilizing, GRPret, test, O, ListMatrGens, ListPermGens, eGen, eList, GRPperm, eSet, eStab, phi;
  n:=Length(TheSpace);
  TheSpaceMod:=Concatenation(TheSpace, TheMod*IdentityMat(n));
  TheAction:=function(eClass, eElt)
    local eVect;
    eVect:=eClass*eElt;
    return List(eVect, x->x mod TheMod);
  end;
  IsStabilizing:=function(TheGRP)
    local eVect, eGen, eSol;
    for eVect in TheSpace
    do
      for eGen in GeneratorsOfGroup(TheGRP)
      do
        eSol:=SolutionIntMat(TheSpaceMod, eVect*eGen);
        if eSol=fail then
          return List(eVect, x->x mod TheMod);
        fi;
      od;
    od;
    return true;
  end;
  GRPret:=Group(GeneratorsOfGroup(GRPmatr));
  while(true)
  do
    test:=IsStabilizing(GRPret);
    if test=true then
      return GRPret;
    fi;
    O:=Orbit(GRPret, test, TheAction);
    ListMatrGens:=GeneratorsOfGroup(GRPret);
    ListPermGens:=[];
    for eGen in ListMatrGens
    do
      eList:=List(O, x->Position(O, TheAction(x, eGen)));
      Add(ListPermGens, PermList(eList));
    od;
    eSet:=Filtered([1..Length(O)], x->SolutionIntMat(TheSpaceMod, O[x])<>fail);
    GRPret:=Stabilizer(GRPret, eSet, ListMatrGens, ListPermGens, OnSets);
  od;
  if IsStabilizing(GRPret)<>true then
    Error("Algorithm error in mod");
  fi;
  return GRPret;
end;






#
#
# for L a linear space of finite index in Z^n
LinearSpace_Stabilizer:=function(GRPmatr, TheSpace)
  local LFact, eList, IsStabilizing, GRPret, TheMod, i;
  IsStabilizing:=function(TheGRP)
    local eVect, eGen, eSol;
    for eVect in TheSpace
    do
      for eGen in GeneratorsOfGroup(TheGRP)
      do
        eSol:=SolutionIntMat(TheSpace, eVect*eGen);
        if eSol=fail then
          return false;
        fi;
      od;
    od;
    return true;
  end;
  if IsStabilizing(GRPmatr) then
    return GRPmatr;
  fi;
  GRPret:=Group(GeneratorsOfGroup(GRPmatr));
  LFact:=LinearSpace_GetDivisor(TheSpace);
  eList:=FactorsInt(LFact);
  for i in [1..Length(eList)]
  do
    TheMod:=Product(eList{[1..i]});
    GRPret:=LinearSpace_ModStabilizer(GRPret, TheSpace, TheMod);
    if IsStabilizing(GRPret) then
      return GRPret;
    fi;
  od;
  if IsStabilizing(GRPret)=false then
    Error("Algorithm error");
  fi;
  return GRPret;
end;


LinearSpace_ModEquivalence:=function(GRPmatr, TheSpace1, TheSpace2, TheMod)
  local n, TheSpace1Mod, TheSpace2Mod, TheAction, IsEquiv, GRPwork, eElt, test, eVect, O, ListMatrGens, ListPermGens, eGen, eList, GRPperm, eSet1, eSet2, eTest, phi, eStab, eMat, TheSpace1work;
  n:=Length(TheSpace1);
  TheSpace1Mod:=Concatenation(TheSpace1, TheMod*IdentityMat(n));
  TheSpace2Mod:=Concatenation(TheSpace2, TheMod*IdentityMat(n));
  TheAction:=function(eClass, eElt)
    local eVect;
    eVect:=eClass*eElt;
    return List(eVect, x->x mod TheMod);
  end;
  IsEquiv:=function(eEquiv)
    local eVect, eGen, eSol;
#    Print("eEquiv=", eEquiv, "\n");
    for eVect in TheSpace1
    do
      eSol:=SolutionIntMat(TheSpace2Mod, eVect*eEquiv);
      if eSol=fail then
#        Print("Leaving eVect=", eVect, "\n");
        return List(eVect*eEquiv, x->x mod TheMod);
      fi;
    od;
    return true;
  end;
  GRPwork:=Group(GeneratorsOfGroup(GRPmatr));
  eElt:=IdentityMat(n);
  while(true)
  do
    test:=IsEquiv(eElt);
    if test=true then
      return rec(GRPwork:=GRPwork, eEquiv:=eElt);
    fi;
    O:=Orbit(GRPwork, test, TheAction);
    ListMatrGens:=GeneratorsOfGroup(GRPwork);
    ListPermGens:=[];
    for eGen in ListMatrGens
    do
      eList:=List(O, x->Position(O, TheAction(x, eGen)));
      Add(ListPermGens, PermList(eList));
    od;
    TheSpace1work:=TheSpace1Mod*eElt;
    eSet1:=Filtered([1..Length(O)], x->SolutionIntMat(TheSpace1work, O[x])<>fail);
    eSet2:=Filtered([1..Length(O)], x->SolutionIntMat(TheSpace2Mod, O[x])<>fail);
    Print("|eSet1|=", Length(eSet1), " |eSet2|=", Length(eSet2), "\n");
    eMat:=RepresentativeAction(GRPwork, eSet1, eSet2, ListMatrGens, ListPermGens, OnSets);
#    Print("After call to RepresentativeAction\n");
    if eMat=fail then
      return fail;
    fi;
#    Print("Before computing GRPwork\n");
    GRPwork:=Stabilizer(GRPwork, eSet2, ListMatrGens, ListPermGens, OnSets);
#    Print("After computing GRPwork\n");
    eElt:=eElt*eMat;
  od;
  for eGen in GeneratorsOfGroup(GRPwork)
  do
    if IsEquiv(GRPwork)<>true then
      Error("Algorithm error in mod");
    fi;
  od;
  return rec(GRPwork:=GRPwork, eEquiv:=eElt);
end;

LinearSpace_Equivalence:=function(GRPmatr, TheSpace1, TheSpace2)
  local n, LFact1, LFact2, eList, IsEquivalence, GRPwork, eElt, TheMod, TheSpace1Img, eTest, i, eDet1, eDet2;
  n:=Length(TheSpace1);
  LFact1:=LinearSpace_GetDivisor(TheSpace1);
  LFact2:=LinearSpace_GetDivisor(TheSpace2);
#  eDet1:=AbsInt(DeterminantMat(TheSpace1));
#  eDet2:=AbsInt(DeterminantMat(TheSpace2));
#  Print("eDet1=", eDet1, " eDet2=", eDet2, "\n");
  Print("LFact1=", LFact1, " LFact2=", LFact2, "\n");
  if LFact1<>LFact2 then
    return fail;
  fi;
  eList:=FactorsInt(LFact1);
  IsEquivalence:=function(eEquiv)
    local eVect, eSol;
    for eVect in TheSpace1
    do
      eSol:=SolutionIntMat(TheSpace2, eVect*eEquiv);
      if eSol=fail then
        return false;
      fi;
    od;
    return true;
  end;
  GRPwork:=Group(GeneratorsOfGroup(GRPmatr));
  eElt:=IdentityMat(n);
  for i in [1..Length(eList)]
  do
    TheMod:=Product(eList{[1..i]});
    Print("i=", i, " TheMod=", TheMod, "\n");
    if IsEquivalence(eElt)=true then
      return eElt;
    fi;
    TheSpace1Img:=List(TheSpace1, x->x*eElt);
    eTest:=LinearSpace_ModEquivalence(GRPwork, TheSpace1Img, TheSpace2, TheMod);
    if eTest=fail then
      return fail;
    fi;
    eElt:=eElt*eTest.eEquiv;
    GRPwork:=eTest.GRPwork;
  od;
  if IsEquivalence(eElt)=false then
    Error("Algorithm error");
  fi;
  return eElt;
end;


# eSet does not have to be left invariant by GRP
OrbitDecomposition:=function(eSet, GRP, eAction)
  local ListOrbitRepr, TotSet, eRepr, eO;
  ListOrbitRepr:=[];
  TotSet:=Set(eSet);
  while(true)
  do
    if Length(TotSet)=0 then
      break;
    fi;
    eRepr:=TotSet[1];
    Add(ListOrbitRepr, eRepr);
    eO:=Orbit(GRP, eRepr, eAction);
    TotSet:=Difference(TotSet, Set(eO));
  od;
  return ListOrbitRepr;
end;
