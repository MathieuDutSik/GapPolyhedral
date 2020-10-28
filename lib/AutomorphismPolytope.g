


VectorConfigurationFullDim_ScalarMat:=function(EXT)
  local n, Qmat, eEXT, Qinv, ScalarMat;
  n:=Length(EXT[1]);
  if Length(EXT)<>Length(Set(EXT)) then
    Error("The vertex list has some repetition");
  fi;
  if RankMat(EXT)<>n then
    Error("The polytope is not of full rank");
  fi;
  Qmat:=NullMat(n,n);
  for eEXT in EXT
  do
    Qmat:=Qmat+TransposedMat([eEXT])*[eEXT];
  od;
  Qinv:=Inverse(Qmat);
  ScalarMat:=EXT*Qinv*TransposedMat(EXT);
  return ScalarMat;
end;



VectorConfigurationFullDim_ScalarMat_AddMat:=function(EXT, ListAddMat)
  local n, Qmat, eEXT, Qinv, ScalarMat, fEXT, eLine, ListMat, LVal;
  n:=Length(EXT[1]);
  if Length(EXT)<>Length(Set(EXT)) then
    Error("The vertex list has some repetition");
  fi;
  if RankMat(EXT)<>n then
    Error("The polytope is not of ful rank");
  fi;
  Qmat:=NullMat(n,n);
  for eEXT in EXT
  do
    Qmat:=Qmat+TransposedMat([eEXT])*[eEXT];
  od;
  Qinv:=Inverse(Qmat);
  ListMat:=Concatenation([Qinv], ListAddMat);
  ScalarMat:=[];
  for eEXT in EXT
  do
    eLine:=[];
    for fEXT in EXT
    do
      LVal:=List(ListMat, x->eEXT*x*fEXT);
      Add(eLine, LVal);
    od;
    Add(ScalarMat, eLine);
  od;
  return ScalarMat;
end;


VectorConfiguration_Invariant_GetTools:=function(EXT, TheLimit)
  local eRec, EXTred, eSelect, n, Qmat, eEXT, Qinv, ListDiagVal, PreListOffDiag, ListOffDiag, iVert, nbVert, eProd;
  eRec:=ColumnReduction(EXT, RankMat(EXT));
  EXTred:=eRec.EXT;
  eSelect:=eRec.Select;
  n:=Length(EXTred[1]);
  Qmat:=NullMat(n,n);
  for eEXT in EXTred
  do
    Qmat:=Qmat+TransposedMat([eEXT])*[eEXT];
  od;
  Qinv:=Inverse(Qmat);
  nbVert:=Length(EXT);
  ListDiagVal:=Set(List([1..nbVert], x->EXTred[x]*Qinv*EXTred[x]));
  if nbVert <= TheLimit then
    PreListOffDiag:=[];
    for iVert in [1..nbVert-1]
    do
      eProd:=EXTred[iVert]*Qinv;
      Append(PreListOffDiag, List([iVert+1..nbVert], x->eProd*EXTred[x]));
    od;
    ListOffDiag:=Set(PreListOffDiag);
  else
    ListOffDiag:=[];
  fi;
  return rec(eSelect:=eSelect, Qinv:=Qinv, TheLimit:=TheLimit, EXTred:=EXTred,
             ListDiagVal:=ListDiagVal,
             ListOffDiag:=ListOffDiag);
end;






DistMat_Invariant:=function(ScalarMat)
  local nbVert, PreListValDiag, PreListNbDiag, iVert, eScal, pos, ePerm, ListValDiag, ListNbDiag, PreListValOff, PreListNbOff, jVert, ListValOff, ListNbOff, TheLimit;
  nbVert:=Length(ScalarMat);
  PreListValDiag:=[];
  PreListNbDiag:=[];
  for iVert in [1..nbVert]
  do
    eScal:=ScalarMat[iVert][iVert];
    pos:=Position(PreListValDiag, eScal);
    if pos=fail then
      Add(PreListValDiag, eScal);
      Add(PreListNbDiag, 1);
    else
      PreListNbDiag[pos]:=PreListNbDiag[pos]+1;
    fi;
  od;
  ePerm:=SortingPerm(PreListValDiag);
  ListValDiag:=Permuted(PreListValDiag, ePerm);
  ListNbDiag:=Permuted(PreListNbDiag, ePerm);
  PreListValOff:=[];
  PreListNbOff:=[];
  TheLimit:=200;
  if nbVert< TheLimit then
    for iVert in [1..nbVert-1]
    do
      for jVert in [iVert+1..nbVert]
      do
        eScal:=ScalarMat[iVert][jVert];
        pos:=Position(PreListValOff, eScal);
        if pos=fail then
          Add(PreListValOff, eScal);
          Add(PreListNbOff, 1);
        else
          PreListNbOff[pos]:=PreListNbOff[pos]+1;
        fi;
      od;
    od;
  fi;
  ePerm:=SortingPerm(PreListValOff);
  ListValOff:=Permuted(PreListValOff, ePerm);
  ListNbOff:=Permuted(PreListNbOff, ePerm);
  return rec(ListValDiag:=ListValDiag, ListNbDiag:=ListNbDiag,
             ListValOff:=ListValOff, ListNbOff:=ListNbOff);
end;





VectorConfiguration_Invariant_Compute:=function(eTool, EXT)
  local EXTred, n, Qmat, eEXT, Qinv, ListValDiag, ListNbDiag, ListValOff, ListNbOff, iVert, jVert, eScal, pos, nbVert, PreListValDiag, PreListNbDiag, PreListValOff, PreListNbOff, ePerm;
  EXTred:=List(EXT, x->x{eTool.eSelect});
  n:=Length(EXTred[1]);
  nbVert:=Length(EXT);
  PreListValDiag:=[];
  PreListNbDiag:=[];
  for iVert in [1..nbVert]
  do
    eScal:=EXTred[iVert]*eTool.Qinv*EXTred[iVert];
    pos:=Position(PreListValDiag, eScal);
    if pos=fail then
      Add(PreListValDiag, eScal);
      Add(PreListNbDiag, 1);
    else
      PreListNbDiag[pos]:=PreListNbDiag[pos]+1;
    fi;
  od;
  ePerm:=SortingPerm(PreListValDiag);
  ListValDiag:=Permuted(PreListValDiag, ePerm);
  ListNbDiag:=Permuted(PreListNbDiag, ePerm);
  PreListValOff:=[];
  PreListNbOff:=[];
  if nbVert< eTool.TheLimit then
    for iVert in [1..nbVert-1]
    do
      for jVert in [iVert+1..nbVert]
      do
        eScal:=EXTred[iVert]*eTool.Qinv*EXTred[jVert];
        pos:=Position(PreListValOff, eScal);
        if pos=fail then
          Add(PreListValOff, eScal);
          Add(PreListNbOff, 1);
        else
          PreListNbOff[pos]:=PreListNbOff[pos]+1;
        fi;
      od;
    od;
  fi;
  ePerm:=SortingPerm(PreListValOff);
  ListValOff:=Permuted(PreListValOff, ePerm);
  ListNbOff:=Permuted(PreListNbOff, ePerm);
  return rec(n:=n,
             ListValDiag:=ListValDiag, ListNbDiag:=ListNbDiag,
             ListValOff:=ListValOff, ListNbOff:=ListNbOff);
end;


VectorConfiguration_Invariant_ComputeAdvanced:=function(eTool, eInc)
  local nbVert, ListScal, nbDiag, nbOff, eVect1, eVect2, eVect3, diffInc, eVal, eV, eScal, pos, eLen, diffLen, eProd, i, j;
  nbVert:=Length(eTool.EXTred);
  nbDiag:=Length(eTool.ListDiagVal);
  eVect1:=ListWithIdenticalEntries(nbDiag,0);
  for eVal in eInc
  do
    eV:=eTool.EXTred[eVal];
    eScal:=eV * eTool.Qinv * eV;
    pos:=Position(eTool.ListDiagVal, eScal);
    eVect1[pos]:=eVect1[pos]+1;
  od;
  if eTool.TheLimit < nbVert then
    return eVect1;
  fi;
  nbOff :=Length(eTool.ListOffDiag);
  eVect2:=ListWithIdenticalEntries(nbOff ,0);
  eVect3:=ListWithIdenticalEntries(nbOff ,0);
  diffInc:=Difference([1..nbVert], eInc);
  eLen:=Length(eInc);
  diffLen:=Length(diffInc);
  for i in [1..eLen]
  do
    eProd:=eTool.EXTred[eInc[i]] * eTool.Qinv;
    for j in [i+1..eLen]
    do
      eScal:=eProd * eTool.EXTred[eInc[j]];
      pos:=Position(eTool.ListOffDiag, eScal);
      eVect2[pos]:=eVect2[pos]+1;
    od;
  od;
  for i in [1..eLen]
  do
    eProd:=eTool.EXTred[eInc[i]] * eTool.Qinv;
    for j in [1..diffLen]
    do
      eScal:=eProd * eTool.EXTred[diffInc[j]];
      pos:=Position(eTool.ListOffDiag, eScal);
      eVect3[pos]:=eVect3[pos]+1;
    od;
  od;
  return Concatenation(eVect1, eVect2, eVect3);
end;






VectorConfiguration_Invariant:=function(EXT, TheLimit)
  local eTool;
  eTool:=VectorConfiguration_Invariant_GetTools(EXT, TheLimit);
  return VectorConfiguration_Invariant_Compute(eTool, EXT);
end;



LinPolytope_Invariant:=function(EXT)
  local TheLimit;
  TheLimit:=500;
  return VectorConfiguration_Invariant(EXT, TheLimit);
end;

LinPolytope_InvariantMD5:=function(EXT)
  local eInv, FileInv, output, eVal, eStr;
  eInv:=LinPolytope_Invariant(EXT);
  FileInv:=Filename(POLYHEDRAL_tmpdir,"TheInv");
  output:=OutputTextFile(FileInv, true);
  AppendTo(output, eInv.n, "\n");
  for eVal in eInv.ListNbDiag
  do
    AppendTo(output, eVal, "\n");
  od;
  for eVal in eInv.ListNbOff
  do
    AppendTo(output, eVal, "\n");
  od;
  for eVal in eInv.ListValDiag
  do
    WriteAll(output, String(eVal));
  od;
  for eVal in eInv.ListValOff
  do
    WriteAll(output, String(eVal));
  od;
  CloseStream(output);
  #
  eStr:=__GetMD5sum(FileInv);
  RemoveFile(FileInv);
  return rec(s:=eStr);
end;

Get_RecScalColor:=function(EXT, GramMat)
  local GetScalarColor, GetLineColor, nbVert;
  GetScalarColor:=function(i,j)
    return EXT[i]*GramMat*EXT[j];
  end;
  GetLineColor:=function(i)
    local eVect;
    eVect:=EXT[i]*GramMat;
    return EXT*eVect;
  end;
  nbVert:=Length(EXT);
  return rec(n:=nbVert,
             GetScalarColor:=GetScalarColor,
             GetLineColor:=GetLineColor);
end;


LinPolytope_Automorphism_Scalable:=function(EXT, GramMat)
  local eRecScalColor;
  eRecScalColor:=Get_RecScalColor(EXT, GramMat);
  return AutomorphismGroupColoredGraph_Scalable(eRecScalColor);
end;



__TheCore_Isomorphism:=function(EXT1, EXT2)
  local ScalarMat1, ScalarMat2, TheReply;
  ScalarMat1:=VectorConfigurationFullDim_ScalarMat(EXT1);
  ScalarMat2:=VectorConfigurationFullDim_ScalarMat(EXT2);
  return IsIsomorphicColoredGraph(ScalarMat1, ScalarMat2);
end;


VectorConfigurationFullDim_Isomorphism:=function(EXT1, EXT2)
  local test, ePerm;
  test:=__TheCore_Isomorphism(EXT1, EXT2);
  if test=false then
    return false;
  else
    ePerm:=PermList(test{[1..Length(EXT1)]});
    return rec(ePerm:=ePerm,
               eMat:=FindTransformation(EXT1, EXT2, ePerm));
  fi;
end;


GeneralWeightMatrix_FullDim_Commuting_Invariant:=function(GramMat, EXT, ListComm)
  local nbVert, GetVectSign, GetSignOff, eSignOff, PreListVal, PreListNb, i, j, eVal, pos, ePerm, ListVal, ListNb;
  nbVert:=Length(EXT);
  GetVectSign:=function(i,j)
    return Concatenation([EXT[i]*GramMat*EXT[j]], List(ListComm, x->EXT[i]*x*GramMat*EXT[j]));
  end;
  GetSignOff:=function(i,j)
    return Set([GetVectSign(i,j), GetVectSign(j,i)]);
  end;
  eSignOff:=Collected(List([1..nbVert], x->GetVectSign(x, x)));
  PreListVal:=[];
  PreListNb:=[];
  for i in [1..nbVert-1]
  do
    for j in [i+1..nbVert]
    do
      eVal:=GetSignOff(i,j);
      pos:=Position(PreListVal, eVal);
      if pos=fail then
        Add(PreListVal, eVal);
        Add(PreListNb, 1);
      else
        PreListNb[pos]:=PreListNb[pos]+1;
      fi;
    od;
  od;
  ePerm:=SortingPerm(PreListVal);
  ListVal:=Permuted(PreListVal, ePerm);
  ListNb:=Permuted(PreListNb, ePerm);
  return rec(eSignOff:=eSignOff, ListNb:=ListNb, ListVal:=ListVal);
end;


GeneralWeightMatrix_FullDim_Commuting:=function(GramMat, EXT, ListComm)
  local n, ListScalarMat, ScalarMat, DiscalarMat, eLine, eEnt, BigDiscalarMat, eVal, iScal, nbDimScal, iEXT, jEXT, nbVert, eCommGen;
  n:=Length(EXT[1]);
  ListScalarMat:=[];
  ScalarMat:=EXT*GramMat*TransposedMat(EXT);
  Add(ListScalarMat, ScalarMat);
  for eCommGen in ListComm
  do
    DiscalarMat:=EXT*eCommGen*GramMat*TransposedMat(EXT);
    Add(ListScalarMat, DiscalarMat);
  od;
  nbVert:=Length(EXT);
  nbDimScal:=Length(ListScalarMat);
  BigDiscalarMat:=[];
  for iEXT in [1..nbVert]
  do
    eLine:=[];
    for jEXT in [1..nbVert]
    do
      eEnt:=[];
      for iScal in [1..nbDimScal]
      do
        eVal:=ListScalarMat[iScal][iEXT][jEXT];
        Add(eEnt, eVal);
      od;
      Add(eLine, eEnt);
    od;
    Add(BigDiscalarMat, eLine);
  od;
  return BigDiscalarMat;
end;

WeightMatrix_FullDim_Commuting:=function(EXT, ListComm)
  local n, Qmat, eEXT, Qinv;
  n:=Length(EXT[1]);
  if Length(EXT)<>Length(Set(EXT)) then
    Error("The vertex list has some repetition");
  fi;
  if RankMat(EXT)<>n then
    Error("The polytope is not of full rank");
  fi;
  Qmat:=NullMat(n,n);
  for eEXT in EXT
  do
    Qmat:=Qmat+TransposedMat([eEXT])*[eEXT];
  od;
  Qinv:=Inverse(Qmat);
  return GeneralWeightMatrix_FullDim_Commuting(Qinv, EXT, ListComm);
end;



LinPolytope_Automorphism_Commuting:=function(EXT, ListComm)
  local BigDiscalarMat, GRP, ePermGen, eMatrGen, eCommGen;
  BigDiscalarMat:=WeightMatrix_FullDim_Commuting(EXT, ListComm);
  GRP:=AutomorphismWeightedDigraph(BigDiscalarMat);
  for ePermGen in GeneratorsOfGroup(GRP)
  do
    eMatrGen:=FindTransformation(EXT, EXT, ePermGen);
    for eCommGen in ListComm
    do
      if eMatrGen*eCommGen<>eCommGen*eMatrGen then
        Error("Commutation error in LinPolytope_Automorphism_Commuting");
      fi;
    od;
  od;
  return GRP;
end;


LinPolytope_Isomorphism_Commuting:=function(EXT1, EXT2, ListComm)
  local BigDiscalarMat1, BigDiscalarMat2, eEquivPerm, eEquivMatr, eCommGen;
  BigDiscalarMat1:=WeightMatrix_FullDim_Commuting(EXT1, ListComm);
  BigDiscalarMat2:=WeightMatrix_FullDim_Commuting(EXT2, ListComm);
  eEquivPerm:=IsIsomorphicWeightDigraph(BigDiscalarMat1, BigDiscalarMat2);
  eEquivMatr:=FindTransformation(EXT1, EXT2, eEquivPerm);
  for eCommGen in ListComm
  do
    if eEquivMatr*eCommGen<>eCommGen*eEquivMatr then
      Error("Commutation error in LinPolytope_Automorphism_Commuting");
    fi;
  od;
  return eEquivPerm;
end;




LinPolytope_Automorphism_Simple:=function(EXT, GramMat)
  local ScalarMat;
  ScalarMat:=EXT*GramMat*TransposedMat(EXT);
  return AutomorphismGroupColoredGraph(ScalarMat);
end;


LinPolytope_Automorphism_GramMat:=function(EXT, GramMat)
  if Length(EXT)<700 then
    return LinPolytope_Automorphism_Simple(EXT, GramMat);
  fi;
  return LinPolytope_Automorphism_Scalable(EXT, GramMat);
end;


Get_QinvMatrix:=function(EXT)
  local n, Qmat, eEXT;
  n:=Length(EXT[1]);
  Qmat:=NullMat(n,n);
  for eEXT in EXT
  do
    Qmat:=Qmat+TransposedMat([eEXT])*[eEXT];
  od;
  return Inverse(Qmat);
end;

LinPolytope_Automorphism:=function(EXT)
  local EXTred, n, Qmat, eEXT, Qinv;
  EXTred:=ColumnReduction(EXT).EXT;
  Qinv:=Get_QinvMatrix(EXTred);
  return LinPolytope_Automorphism_GramMat(EXTred, Qinv);
end;




GetScalarMatrix_PolytopeStabSubset:=function(EXT, EXTsub)
  local eSet, EXTred, ScalarMat, nbVert, RedoneScalarMat, eLine, iVert, jVert, eValMatr, eVal;
  eSet:=Set(List(EXTsub, x->Position(EXT, x)));
  EXTred:=ColumnReduction(EXT, RankMat(EXT)).EXT;
  ScalarMat:=VectorConfigurationFullDim_ScalarMat(EXTred);
  nbVert:=Length(EXTred);
  RedoneScalarMat:=[];
  for iVert in [1..nbVert]
  do
    eLine:=[];
    for jVert in [1..nbVert]
    do
      eValMatr:=ScalarMat[iVert][jVert];
      if iVert<>jVert then
        Add(eLine, eValMatr);
      else
        if iVert in eSet then
          eVal:=1;
        else
          eVal:=0;
        fi;
        Add(eLine, [eValMatr, eVal]);
      fi;
    od;
    Add(RedoneScalarMat, eLine);
  od;
  return RedoneScalarMat;
end;

LinPolytope_AutomorphismStabSubset:=function(EXT, EXTsub)
  local RedoneScalarMat;
  RedoneScalarMat:=GetScalarMatrix_PolytopeStabSubset(EXT, EXTsub);
  return AutomorphismGroupColoredGraph(RedoneScalarMat);
end;


LinPolytope_IsomorphismStabSubset:=function(EXT1, EXTsub1, EXT2, EXTsub2)
  local RedoneScalarMat1, RedoneScalarMat2, eEquiv;
  RedoneScalarMat1:=GetScalarMatrix_PolytopeStabSubset(EXT1, EXTsub1);
  RedoneScalarMat2:=GetScalarMatrix_PolytopeStabSubset(EXT2, EXTsub2);
  eEquiv:=IsIsomorphicEdgeColoredGraph(RedoneScalarMat1, RedoneScalarMat2);
  if eEquiv=false then
    return false;
  fi;
  return PermList(eEquiv);
end;




GetScalarMatrix_PolytopeStabSubset_AddMat:=function(EXT, EXTsub, ListAddMat)
  local eSet, EXTred, ScalarMat, nbVert, RedoneScalarMat, eLine, iVert, jVert, eValMatr, eVal;
  eSet:=Set(List(EXTsub, x->Position(EXT, x)));
  if RankMat(EXT)<>Length(EXT[1]) then
    Error("Rank error in _AddMat function");
  fi;
  ScalarMat:=VectorConfigurationFullDim_ScalarMat_AddMat(EXT, ListAddMat);
  nbVert:=Length(EXT);
  RedoneScalarMat:=[];
  for iVert in [1..nbVert]
  do
    eLine:=[];
    for jVert in [1..nbVert]
    do
      eValMatr:=ScalarMat[iVert][jVert];
      if iVert<>jVert then
        Add(eLine, eValMatr);
      else
        if iVert in eSet then
          eVal:=1;
        else
          eVal:=0;
        fi;
        Add(eLine, [eValMatr, eVal]);
      fi;
    od;
    Add(RedoneScalarMat, eLine);
  od;
  return RedoneScalarMat;
end;





GetScalarMatrixInvariant_PolytopeStabSubset_AddMat:=function(EXT, EXTsub, ListAddMat)
  local eSet, nbVert, GetValue, PreListValues, ListValues, iVert, jVert, eVal, pos, nbValues, ListOccDiag, ListOccOff;
  eSet:=Set(List(EXTsub, x->Position(EXT, x)));
  if RankMat(EXT)<>Length(EXT[1]) then
    Error("Rank error in _AddMat function");
  fi;
  nbVert:=Length(EXT);
  GetValue:=function(i, j)
    local eLine, eMat;
    eLine:=[];
    for eMat in ListAddMat
    do
      Add(eLine, EXT[i] * eMat * EXT[j]);
    od;
    if i=j then
      if i in eSet then
        Add(eLine, 1);
      else
        Add(eLine, 0);
      fi;
    fi;
    return eLine;
  end;
  PreListValues:=[];
  for iVert in [1..nbVert]
  do
    for jVert in [1..nbVert]
    do
      eVal:=GetValue(iVert, jVert);
      if Position(PreListValues, eVal)=fail then
        Add(PreListValues, eVal);
      fi;
    od;
  od;
  ListValues:=Set(PreListValues);
  nbValues:=Length(ListValues);
  ListOccDiag:=ListWithIdenticalEntries(nbValues, 0);
  for iVert in [1..nbVert]
  do
    eVal:=GetValue(iVert, iVert);
    pos:=Position(ListValues, eVal);
    ListOccDiag[pos]:=ListOccDiag[pos] + 1;
  od;
  ListOccOff:=ListWithIdenticalEntries(nbValues, 0);
  for iVert in [1..nbVert]
  do
    for jVert in [1..nbVert]
    do
      if iVert<>jVert then
        eVal:=GetValue(iVert, jVert);
        pos:=Position(ListValues, eVal);
        ListOccOff[pos]:=ListOccOff[pos] + 1;
      fi;
    od;
  od;
  return rec(ListValues:=ListValues, ListOccDiag:=ListOccDiag, ListOccOff:=ListOccOff);
end;






Get_RecScalColor_Subset_AddMat:=function(EXT, EXTsub, ListAddMat)
  local eSet, GetScalarColor, GetLineColor, nbVert;
  eSet:=Set(List(EXTsub, x->Position(EXT, x)));
  nbVert:=Length(EXT);
  GetScalarColor:=function(i, j)
    local eLine, eMat;
    eLine:=[];
    for eMat in ListAddMat
    do
      Add(eLine, EXT[i] * eMat * EXT[j]);
    od;
    if i=j then
      if i in eSet then
        Add(eLine, 1);
      else
        Add(eLine, 0);
      fi;
    fi;
    return eLine;
  end;
  GetLineColor:=function(i)
    return List([1..nbVert], x->GetScalarColor(x, i));
  end;
  return rec(n:=nbVert,
             GetScalarColor:=GetScalarColor,
             GetLineColor:=GetLineColor);
end;




LinPolytope_AutomorphismStabSubset_AddMat:=function(EXT, EXTsub, ListAddMat)
  local RecTool;
  RecTool:=Get_RecScalColor_Subset_AddMat(EXT, EXTsub, ListAddMat);
  return AutomorphismGroupColoredGraph_Scalable(RecTool);
end;


LinPolytope_IsomorphismStabSubset_AddMat:=function(EXT1, EXTsub1, EXT2, EXTsub2, ListAddMat1, ListAddMat2)
  local RedoneScalarMat1, RedoneScalarMat2, eEquiv;
  RedoneScalarMat1:=GetScalarMatrix_PolytopeStabSubset_AddMat(EXT1, EXTsub1, ListAddMat1);
  RedoneScalarMat2:=GetScalarMatrix_PolytopeStabSubset_AddMat(EXT2, EXTsub2, ListAddMat2);
  eEquiv:=IsIsomorphicColoredGraph(RedoneScalarMat1, RedoneScalarMat2);
  if eEquiv=false then
    return false;
  fi;
  return PermList(eEquiv);
end;





LinPolytope_Automorphism_MemoryEff:=function(EXT, eRecStrategy)
  local nbVert, eTool, GRPreturn, iDist, eDist, Gra, iExt, jExt, IsAnAutomorphismGroup, ListRank, ListOrdered, SetRank, Pos, i, j, u, GetGroupForValue, GetGroupForValue_meth1, GetGroupForValue_meth2, eSetV, eSortPerm, EXTred, ListSizes, SetV, TheLimit, iVert, jVert, eScal, pos, ListFreq, GetSetV, GetListFreq, ListFreqInv, eGRP, nbDist;
  TheLimit:=-467;
  EXTred:=ColumnReduction(EXT).EXT;
  eTool:=VectorConfiguration_Invariant_GetTools(EXTred, TheLimit);
  nbVert:=Length(EXT);
  GetSetV:=function()
    local iVert, jVert, eScal;
    SetV:=[];
    for iVert in [1..nbVert-1]
    do
      for jVert in [iVert+1..nbVert]
      do
        eScal:=EXTred[iVert]*eTool.Qinv*EXTred[jVert];
        AddSet(SetV, eScal);
      od;
    od;
    nbDist:=Length(SetV);
  end;
  IsAnAutomorphismGroup:=function(GRP)
    local eGen, i, j, i2, j2, eScal1, eScal2;
    for eGen in GeneratorsOfGroup(GRP)
    do
      for i in [1..nbVert-1]
      do
        for j in [i..nbVert]
        do
          i2:=OnPoints(i, eGen);
          j2:=OnPoints(j, eGen);
          eScal1:=EXTred[i]*eTool.Qinv*EXTred[j];
          eScal2:=EXTred[i2]*eTool.Qinv*EXTred[j2];
          if eScal1<>eScal2 then
            return false;
          fi;
        od;
      od;
    od;
    return true;
  end;
  GetGroupForValue_meth1:=function(iDist)
    local GRA, iExt, jExt, eScal, ListAdjacency, LAdj, ThePartition, ListColor, iDistCurr, nbEdge, SetDist, nbColor;
    GRA:=NullGraph(Group(()), nbVert);
    iDistCurr:=iDist-1;
    SetDist:=[];
    while(true)
    do
      iDistCurr:=iDistCurr+1;
      AddSet(SetDist, eSetV[iDistCurr]);
      #
      ListAdjacency:=[];
      nbEdge:=0;
      for iExt in [1..nbVert]
      do
        LAdj:=[];
        for jExt in [1..nbVert]
        do
          eScal:=EXTred[iExt]*eTool.Qinv*EXTred[jExt];
          if eScal in SetDist and iExt<>jExt then
            Add(LAdj, jExt);
            nbEdge:=nbEdge+1;
          fi;
        od;
        Add(ListAdjacency, LAdj);
      od;
      ListColor:=GetConnectedComponentsListAdj(ListAdjacency);
      nbColor:=Maximum(ListColor);
      Print("|SetDist|=", Length(SetDist), " nbEdge=", nbEdge, " nbColor=", nbColor, "\n");
      if nbColor=1 then
        break;
      fi;
    od;
    ThePartition:=[[1..nbVert]];
    return SymmetryGroupVertexColoredGraphAdjList(ListAdjacency, ThePartition);
  end;
  GetGroupForValue_meth2:=function(iDist)
    local GRA, iExt, jExt, eScal, ListAdjacency, LAdj, ThePartition, ListColor, iDistCurr, nbEdge, SetDist, nbColor, ListStatusBreaking, iDistFound, pos, i;
    GRA:=NullGraph(Group(()), nbVert);
    iDistCurr:=iDist;
    SetDist:=[];
    ListColor:=[1..nbVert];
    while(true)
    do
      nbColor:=Maximum(ListColor);
      ListStatusBreaking:=ListWithIdenticalEntries(nbDist, 0);
      for iExt in [1..nbVert]
      do
        LAdj:=[];
        for jExt in [1..nbVert]
        do
          if ListColor[iExt]<>ListColor[jExt] then
            eScal:=EXTred[iExt]*eTool.Qinv*EXTred[jExt];
            pos:=Position(eSetV, eScal);
            ListStatusBreaking[pos]:=1;
          fi;
        od;
      od;
      iDistFound:=-1;
      for i in [iDistCurr..nbDist]
      do
        if iDistFound=-1 then
          if ListStatusBreaking[i]=1 then
            iDistFound:=i;
          fi;
        fi;
      od;
      if iDistFound=-1 then
        Error("Program cannot work");
      fi;
      Print("iDistFound=", iDistFound, "\n");
      iDistCurr:=iDistFound;
      #
      AddSet(SetDist, eSetV[iDistCurr]);
      ListAdjacency:=[];
      nbEdge:=0;
      for iExt in [1..nbVert]
      do
        LAdj:=[];
        for jExt in [1..nbVert]
        do
          eScal:=EXTred[iExt]*eTool.Qinv*EXTred[jExt];
          if eScal in SetDist and iExt<>jExt then
            Add(LAdj, jExt);
            nbEdge:=nbEdge+1;
          fi;
        od;
        Add(ListAdjacency, LAdj);
      od;
      ListColor:=GetConnectedComponentsListAdj(ListAdjacency);
      nbColor:=Maximum(ListColor);
      Print("|SetDist|=", Length(SetDist), " nbEdge=", nbEdge, " nbColor=", nbColor, "\n");
      if nbColor=1 then
        break;
      fi;
    od;
    ThePartition:=[[1..nbVert]];
    return SymmetryGroupVertexColoredGraphAdjList(ListAdjacency, ThePartition);
  end;
  GetGroupForValue:=function(iDist)
    return GetGroupForValue_meth2(iDist);
  end;
  GetSetV();
  if eRecStrategy.method="frequency" then
    ListFreqInv:=List(ListFreq, x->1/x);
    eSortPerm:=SortingPerm(ListFreqInv);
  elif eRecStrategy.method="group size" then
    ListSizes:=List([1..Length(SetV)], x->Order(GetGroupForValue(x)));
    eSortPerm:=SortingPerm(ListSizes);
  elif eRecStrategy.method="first small group" then
    pos:=First([1..Length(SetV)], x->Order(GetGroupForValue(x)) < eRecStrategy.StartingSize);
    if pos=1 then
      eSortPerm:=();
    else
      eSortPerm:=(1, pos);
    fi;
  else
    Error("Please put here what you have in mind");
  fi;
  eSetV:=Permuted(SetV, eSortPerm);
  for iDist in [1..Length(eSetV)]
  do
    Print("iDist=", iDist, "\n");
    eDist:=eSetV[iDist];
    if iDist>1 then
      if IsAnAutomorphismGroup(GRPreturn)=true then
        return GRPreturn;
      fi;
      Print("   We have to continue further\n");
    fi;
    if iDist=1 then
      GRPreturn:=GetGroupForValue(iDist);
      Print("   aft1\n");
    else
      eGRP:=GetGroupForValue(iDist);
      Print("   aft2\n");
      Print("   |eGRP|=", Order(eGRP), " now computing intersection\n");
      GRPreturn:=Intersection(GRPreturn, eGRP);
    fi;
    Print("   We have GRPreturn\n");
    Print("   |GRPreturn|=", Order(GRPreturn), "\n");
  od;
  if IsAnAutomorphismGroup(GRPreturn)=false then
    Error("Apparently the group is not an automorphism group");
  fi;
  return GRPreturn;
end;







LinPolytope_Isomorphism_Simple:=function(EXT1, GramMat1, EXT2, GramMat2)
  local eEquiv, ScalarMat1, ScalarMat2;
  ScalarMat1:=EXT1*GramMat1*TransposedMat(EXT1);
  ScalarMat2:=EXT2*GramMat2*TransposedMat(EXT2);
  eEquiv:=IsIsomorphicColoredGraph(ScalarMat1, ScalarMat2);
  if eEquiv=false then
    return false;
  fi;
  return PermList(eEquiv);
end;

LinPolytope_Isomorphism_Scalable:=function(EXT1, GramMat1, EXT2, GramMat2)
  local eRecScalColor1, eRecScalColor2, eEquiv;
  eRecScalColor1:=Get_RecScalColor(EXT1, GramMat1);
  eRecScalColor2:=Get_RecScalColor(EXT2, GramMat2);
  eEquiv:=IsIsomorphicColoredGraph_Scalable(eRecScalColor1, eRecScalColor2);
  if eEquiv=false then
    return false;
  fi;
  return PermList(eEquiv);
end;

LinPolytope_Isomorphism_GramMat:=function(EXT1, GramMat1, EXT2, GramMat2)
  if Length(EXT1)<>Length(EXT2) then
    return false;
  fi;
  if Length(EXT1)<700 then
    return LinPolytope_Isomorphism_Simple(EXT1, GramMat1, EXT2, GramMat2);
  fi;
  return LinPolytope_Isomorphism_Scalable(EXT1, GramMat1, EXT2, GramMat2);
end;

LinPolytope_Isomorphism:=function(EXT1, EXT2)
  local EXTred1, EXTred2, Qinv1, Qinv2;
  EXTred1:=ColumnReduction(EXT1).EXT;
  EXTred2:=ColumnReduction(EXT2).EXT;
  Qinv1:=Get_QinvMatrix(EXTred1);
  Qinv2:=Get_QinvMatrix(EXTred2);
  return LinPolytope_Isomorphism_GramMat(EXTred1, Qinv1, EXTred2, Qinv2);
end;


# Some polytope with more than 10000 vertices are hard
# to determine isomorphism of. Here we provide an heuristic
# solution that works in some cases.
LinPolytope_IsomorphismHeuristic:=function(EXT1, EXT2)
  local EXTred1, EXTred2, dim, nbVert, eSumMat1, eEXT, eInv1, eSumMat2, eInv2, ListDiag1, ListDiag2, Coll1, Coll2, SetVal, eVal, ListAdmi, eRec, eSet1, eSet2, EXTsel1, EXTsel2, eEquiv, eMat, eList;
  EXTred1:=ColumnReduction(EXT1).EXT;
  EXTred2:=ColumnReduction(EXT2).EXT;
  dim:=Length(EXT1[1]);
  nbVert:=Length(EXT1);
  if dim<>Length(EXT2[1]) or nbVert<>Length(EXT2) then
    return false;
  fi;
  eSumMat1:=NullMat(dim,dim);
  for eEXT in EXTred1
  do
    eSumMat1:=eSumMat1 + TransposedMat([eEXT])*[eEXT];
  od;
  eInv1:=Inverse(eSumMat1);
  eSumMat2:=NullMat(dim,dim);
  for eEXT in EXTred2
  do
    eSumMat2:=eSumMat2 + TransposedMat([eEXT])*[eEXT];
  od;
  eInv2:=Inverse(eSumMat2);
  ListDiag1:=List(EXTred1, x->x*eInv1*x);
  ListDiag2:=List(EXTred2, x->x*eInv2*x);
  Coll1:=Collected(ListDiag1);
  Coll2:=Collected(ListDiag2);
  if Set(Coll1)<>Set(Coll2) then
    return false;
  fi;
  SetVal:=Set(List(Coll1, x->x[2]));
  for eVal in SetVal
  do
    ListAdmi:=[];
    for eRec in Coll1
    do
      if eRec[2]<=eVal then
        Add(ListAdmi, eRec[1]);
      fi;
    od;
    eSet1:=Filtered([1..nbVert], x->Position(ListAdmi, ListDiag1[x])<>fail);
    eSet2:=Filtered([1..nbVert], x->Position(ListAdmi, ListDiag2[x])<>fail);
    EXTsel1:=EXTred1{eSet1};
    EXTsel2:=EXTred2{eSet2};
    eEquiv:=LinPolytope_Isomorphism(EXTsel1, EXTsel2);
    if eEquiv=false then
      return false;
    fi;
    eMat:=FindTransformation(EXTsel1, EXTsel2, eEquiv);
    eList:=List(EXTred1, x->Position(EXTred2, x*eMat));
    if Position(eList, fail)=fail then
      return PermList(eList);
    fi;
  od;
  return false;
end;

CanonicalReorderingVertices:=function(EXT)
  local nbVert, ScalarMat, CanonDesc, EXTcan, iCan, iOrig, eBigMat, eInvMat, EXT_ret;
  nbVert:=Length(EXT);
  ScalarMat:=VectorConfigurationFullDim_ScalarMat(EXT);
  CanonDesc:=CanonicalFormColoredGraph(ScalarMat);
  EXTcan:=[];
  for iCan in [1..nbVert]
  do
    iOrig:=CanonDesc.CanonicalList[iCan];
    Add(EXTcan, EXT[iOrig]);
  od;
  return rec(EXT:=EXTcan,
             CanonicalList:=CanonDesc.CanonicalList,
             CanonicalRevList:=CanonDesc.CanonicalRevList);
end;


#
# We return an ordering of the vertices that is canonical.
# The coordinates of the vertices themselves are not canonical.
LinPolytope_CanonicalForm:=function(EXT)
  local eRecRewrite, eBigMat, eInvMat, EXT_ret;
  eRecRewrite:=CanonicalReorderingVertices(EXT);
  eBigMat:=RowReduction(eRecRewrite.EXT).EXT;
  eInvMat:=Inverse(eBigMat);
  EXT_ret:=eRecRewrite.EXT * eInvMat;
  return rec(EXT:=EXT_ret,
             CanonicalList:=eRecRewrite.CanonicalList,
             CanonicalRevList:=eRecRewrite.CanonicalRevList);
end;


LinPolytopeIntegral_CanonicalForm:=function(EXT)
  local eRecRewrite, EXT_ret;
  eRecRewrite:=CanonicalReorderingVertices(EXT);
  EXT_ret:=TransposedMat(HermiteNormalFormIntegerMat(TransposedMat(eRecRewrite.EXT)));
  return rec(EXT:=EXT_ret,
             CanonicalList:=eRecRewrite.CanonicalList,
             CanonicalRevList:=eRecRewrite.CanonicalRevList);

end;







LinPolytopeIntegral_Isomorphism_Exhaustive:=function(EXT1, EXT2)
  local eEquiv, GRP, eElt, nEquiv, eBigMat;
  eEquiv:=LinPolytope_Isomorphism(EXT1, EXT2);
  if eEquiv=false then
    return false;
  fi;
  GRP:=LinPolytope_Automorphism(EXT1);
  for eElt in GRP
  do
    nEquiv:=eElt*eEquiv;
    eBigMat:=FindTransformation(EXT1, EXT2, nEquiv);
    if IsIntegralMat(eBigMat) then
      return eBigMat;
    fi;
  od;
  return false;
end;


LinPolytopeIntegral_Automorphism_Exhaustive:=function(EXT)
  local n, eElt, eBigMat, ListPermGens, ListMatrGens, ThePermGrp, TheMatrGrp, FuncInsert, GRP;
  n:=Length(EXT[1]);
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
  GRP:=LinPolytope_Automorphism(EXT);
  for eElt in GRP
  do
    eBigMat:=FindTransformation(EXT, EXT, eElt);
    if IsIntegralMat(eBigMat) then
      FuncInsert(eElt, eBigMat);
    fi;
  od;
  TheMatrGrp:=PersoGroupMatrix(ListMatrGens, n);
  SetSize(TheMatrGrp, Order(ThePermGrp));
  return rec(GRPmatr:=TheMatrGrp, GRPperm:=ThePermGrp);
end;






KernelLinPolytopeIntegral_Isomorphism_Subspaces:=function(EXT1, EXT2, GRP2, eEquiv)
  local n, eBasis1, eBasis2, EXTbas1, EXTbas2, TheMatEquiv, ListMatrGens, eGen, TheMat, GRPspace, eLatt1, eLatt2, eRec1, eRec2, eSpaceEquiv, eMatFinal;
  Print("Begin KernelLinPolytopeIntegral_Isomorphism_Subspaces\n");
  n:=Length(EXT1[1]);
  eBasis1:=GetZbasis(EXT1);
  eBasis2:=GetZbasis(EXT2);
  EXTbas1:=List(EXT1, x->SolutionMat(eBasis1, x));
  EXTbas2:=List(EXT2, x->SolutionMat(eBasis2, x));
  TheMatEquiv:=FindTransformation(EXTbas1, EXTbas2, eEquiv);
  ListMatrGens:=[];
  for eGen in GeneratorsOfGroup(GRP2)
  do
    TheMat:=FindTransformation(EXTbas2, EXTbas2, eGen);
    Add(ListMatrGens, TheMat);
  od;
  GRPspace:=Group(ListMatrGens);
  eLatt1:=Inverse(eBasis1)*TheMatEquiv;
  eLatt2:=Inverse(eBasis2);
  eRec1:=RemoveFractionMatrixPlusCoef(eLatt1);
  eRec2:=RemoveFractionMatrixPlusCoef(eLatt2);
  if eRec1.TheMult<>eRec2.TheMult then
    return false;
  fi;
  eSpaceEquiv:=LinearSpace_Equivalence(GRPspace, eRec1.TheMat, eRec2.TheMat);
  if eSpaceEquiv=fail then
    return false;
  fi;
  eMatFinal:=Inverse(eBasis1)*TheMatEquiv*eSpaceEquiv*eBasis2;
  if IsIntegralMat(eMatFinal)=false then
    Error("eMatFinal is not integral, BUG");
  fi;
  if Set(EXT1*eMatFinal)<>Set(EXT2) then
    Error("eMatFinal does not map the polytopes, BUG");
  fi;
  return eMatFinal;
end;


LinPolytopeIntegral_Isomorphism_Subspaces:=function(EXT1, EXT2)
  local n, eEquiv, GRP2;
  n:=Length(EXT1[1]);
  if Length(EXT2[1])<>n then
    Error("The dimension of EXT1 and EXT2 are not the same");
  fi;
  if RankMat(EXT1)<>n then
    Error("EXT1 is not full dimensional");
  fi;
  if RankMat(EXT2)<>n then
    Error("EXT2 is not full dimensional");
  fi;
  eEquiv:=LinPolytope_Isomorphism(EXT1, EXT2);
  if eEquiv=false then
    return false;
  fi;
  GRP2:=LinPolytope_Automorphism(EXT2);
  return KernelLinPolytopeIntegral_Isomorphism_Subspaces(EXT1, EXT2, GRP2, eEquiv);
end;



KernelLinPolytopeIntegral_Automorphism_Subspaces:=function(EXT, GRP)
  local n, eBasis, EXTbas, ListPermGens, ListMatrGens, eGen, TheMat, GRPmatr, LattToStab, eStab, eList, ePerm, eMatr, GRPpermFinal, GRPmatrFinal;
  n:=Length(EXT[1]);
  if RankMat(EXT)<>n then
    Error("Wrong rank for LinPolytopeIntegral_Automorphism");
  fi;
  eBasis:=GetZbasis(EXT);
  EXTbas:=List(EXT, x->SolutionMat(eBasis, x));
  ListPermGens:=GeneratorsOfGroup(GRP);
  ListMatrGens:=List(ListPermGens, eGen->FindTransformation(EXTbas, EXTbas, eGen));
  GRPmatr:=Group(ListMatrGens);
  LattToStab:=RemoveFractionMatrix(Inverse(eBasis));
  #
  eStab:=LinearSpace_Stabilizer(GRPmatr, LattToStab);
  ListPermGens:=[];
  ListMatrGens:=[];
  for eGen in GeneratorsOfGroup(eStab)
  do
    eList:=List(EXTbas, x->Position(EXTbas, x*eGen));
    ePerm:=PermList(eList);
    eMatr:=FindTransformation(EXT, EXT, ePerm);
    if IsIntegralMat(eMatr)=false then
      Error("Some bugs to resolve");
    fi;
    Add(ListPermGens, ePerm);
    Add(ListMatrGens, eMatr);
  od;
  GRPmatrFinal:=Group(ListMatrGens);
  GRPpermFinal:=Group(ListPermGens);
  SetSize(GRPmatrFinal, Order(GRPpermFinal));
  return rec(GRPperm:=GRPpermFinal, GRPmatr:=GRPmatrFinal);
end;

LinPolytopeIntegral_Automorphism_Subspaces:=function(EXT)
  local GRP;
  GRP:=LinPolytope_Automorphism(EXT);
  return KernelLinPolytopeIntegral_Automorphism_Subspaces(EXT, GRP);
end;


LinPolytopeIntegral_Automorphism:=function(EXT)
  local GRP;
  GRP:=LinPolytope_Automorphism(EXT);
  if Order(GRP)<=10000 then
    return LinPolytopeIntegral_Automorphism_Exhaustive(EXT);
  fi;
  return LinPolytopeIntegral_Automorphism_Subspaces(EXT);
end;



# Define GRPint = GRP inter GLn(Z)
# Define true if the index GRP/GRPint is smaller than UpperLimit
# and false otherwise.
LinPolytopeIntegral_EstimateQuotient:=function(GRP, UpperLimit)
  local ListGen, n, ListSubspace, FuncInsert, nbSub, IsFinished, iSub, eGen, NewSub;
  ListGen:=GeneratorsOfGroup(GRP);
  n:=Length(ListGen[1]);
  ListSubspace:=[];
  FuncInsert:=function(eSub)
    local eInv, eRec;
    eInv:=Inverse(eSub);
    for eRec in ListSubspace
    do
      if IsIntegralMat(eRec.eSub*eInv)=true then
        return;
      fi;
    od;
    Add(ListSubspace, rec(eSub:=eSub, status:=false));
  end;
  FuncInsert(IdentityMat(n));
  while(true)
  do
    nbSub:=Length(ListSubspace);
    IsFinished:=true;
    for iSub in [1..nbSub]
    do
      if ListSubspace[iSub].status=false then
        ListSubspace[iSub].status:=true;
        IsFinished:=false;
        for eGen in ListGen
        do
          NewSub:=ListSubspace[iSub].eSub*eGen;
          FuncInsert(NewSub);
          if Length(ListSubspace) > UpperLimit then
            return false;
          fi;
        od;
      fi;
    od;
    if IsFinished=true then
      break;
    fi;
  od;
  return true;
end;



LinPolytopeIntegral_Isomorphism:=function(EXT1, EXT2)
  local GRP1;
  GRP1:=LinPolytope_Automorphism(EXT1);
  if Order(GRP1)<=10000 then
    return LinPolytopeIntegral_Isomorphism_Exhaustive(EXT1, EXT2);
  fi;
  return LinPolytopeIntegral_Isomorphism_Subspaces(EXT1, EXT2);
end;


# Search for the automorphism preserving a linear subspace as well.
LinPolytopeSubspace_Automorphism:=function(EXT, TheSpace)
  local eRec, EXTred, TheSpaceRed, n, Qmat, eEXT, Qinv, TheOrth, TotalBasis, DimSpace, MatrixProj, i, eVect, eSol, eVectProj, iSpace, ListComm;
  eRec:=ColumnReduction(EXT);
  EXTred:=List(EXT, x->x{eRec.Select});
  TheSpaceRed:=List(TheSpace, x->x{eRec.Select});
  n:=Length(EXTred[1]);
  #
  # Computing the invariant scalar product
  #
  Qmat:=NullMat(n,n);
  for eEXT in EXTred
  do
    Qmat:=Qmat+TransposedMat([eEXT])*[eEXT];
  od;
  Qinv:=Inverse(Qmat);
  #
  # Computing the orthogonal projection
  #
  TheOrth:=NullspaceMat(TransposedMat(TheSpaceRed*Qinv));
  TotalBasis:=Concatenation(TheSpaceRed, TheOrth);
  DimSpace:=Length(TheSpaceRed);
  MatrixProj:=[];
  for i in [1..n]
  do
    eVect:=ListWithIdenticalEntries(n,0);
    eVect[i]:=1;
    eSol:=SolutionMat(TotalBasis, eVect);
    eVectProj:=ListWithIdenticalEntries(n,0);
    for iSpace in [1..DimSpace]
    do
      eVectProj:=eVectProj + eSol[iSpace]*TheSpaceRed[iSpace];
    od;
    Add(MatrixProj, eVectProj);
  od;
  ListComm:=[MatrixProj];
  return LinPolytope_Automorphism_Commuting(EXTred, ListComm);
end;
