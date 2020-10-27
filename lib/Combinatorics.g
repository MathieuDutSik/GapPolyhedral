InitialSub:=function(n, k)
  return [1..k];
end;


NextSubset:=function(n, eList)
  local k, aPos, iter, h, v;
  k:=Length(eList);
  aPos:=k;
  iter:=0;
  while(true)
  do
    if eList[aPos]<n-iter then
      h:=eList[aPos]+1;
      for v in [aPos..k]
      do
        eList[v]:=h;
        h:=h+1;
      od;
      return eList;
    fi;
    aPos:=aPos-1;
    iter:=iter+1;
    if aPos=0 then
      return false;
    fi;
  od;
end;


HadamardMatrixPowerOfTwo:=function(n)
  local LInt, nSma, Hsma, Hret, i, j;
  if n=1 then
    return [[1]];
  fi;
  LInt:=FactorsInt(n);
  if Set(LInt)<>[2] then
    Error("n should be a power of 2");
  fi;
  nSma:=n/2;
  Hsma:=HadamardMatrixPowerOfTwo(nSma);
  Hret:=NullMat(n,n);
  for i in [1..nSma]
  do
    for j in [1..nSma]
    do
      Hret[i][j]:=Hsma[i][j];
      Hret[i+nSma][j]:=-Hsma[i][j];
      Hret[i+nSma][j+nSma]:=Hsma[i][j];
      Hret[i][j+nSma]:=Hsma[i][j];
    od;
  od;
  return Hret;
end;


SantosVallentinSchurmannConstruction:=function(n)
  local d, HadMat, MapMatrix, HadamardSimplex, i, j, HadamardSimplexRaw, HadamardSimplexZeroOrig, TheSpace, TheBasis, GramMat, HadamardSimplex_NB, TheSimplex, HtildeMatrix;
  d:=2^n-1;
  HadMat:=HadamardMatrixPowerOfTwo(d+1);
  MapMatrix:=function(uMat)
    local nbRow, nbCol, RetMat, i, j, eVal, eVal2;
    nbRow:=Length(uMat);
    nbCol:=Length(uMat[1]);
    RetMat:=NullMat(nbRow,nbCol);
    for i in [1..nbRow]
    do
      for j in [1..nbCol]
      do
        eVal:=uMat[i][j];
        if eVal=1 then
          eVal2:=0;
        fi;
        if eVal=-1 then
          eVal2:=1;
        fi;
        RetMat[i][j]:=eVal2;
      od;
    od;
    return RetMat;
  end;
  HtildeMatrix:=MapMatrix(HadMat{[2..d+1]});
  HadamardSimplexRaw:=TransposedMat(HtildeMatrix);
  HadamardSimplexZeroOrig:=List(HadamardSimplexRaw, x->x-HadamardSimplexRaw[1]);
  #
  TheSpace:=Concatenation(HadamardSimplexRaw, 2*IdentityMat(d));
  TheBasis:=GetZbasis(TheSpace);
  GramMat:=TheBasis * TransposedMat(TheBasis);
  HadamardSimplex_NB:=List(HadamardSimplexZeroOrig, x->SolutionIntMat(TheBasis, x));
  TheSimplex:=List(HadamardSimplex_NB, x->Concatenation([1], x));
  return rec(GramMat:=GramMat, TheSimplex:=TheSimplex);
end;





InitialDirectProduct:=function(ListLen)
  return ListWithIdenticalEntries(Length(ListLen),1);
end;

NextDirectProduct:=function(ListLen, eList)
  local k, xpos, i, retList;
  k:=Length(ListLen);
  xpos:=-1;
  for i in [1..k]
  do
    if xpos=-1 then
      if eList[i]<ListLen[i] then
        xpos:=i;
      fi;
    fi;
  od;
  if xpos=-1 then
    return false;
  fi;
  retList:=[];
  for i in [1..xpos-1]
  do
    Add(retList, 1);
  od;
  Add(retList, eList[xpos]+1);
  for i in [xpos+1..k]
  do
    Add(retList, eList[i]);
  od;
  return retList;
end;

