FileDR2:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"dreadnaut");
FileNautyGroupGAP:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"NautyGroupToGAP_sec");
FileNautyIsoOutputGAP:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"NautyIsoOutputToGAP");
FileNautyReadCanon:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"NautyReadCanon");
FileAMTOG:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"amtog");
FileMD5read:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"MD5_to_read");
FileNautyGraph6Expression:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"NautyGraph6Expression");
FileGENG:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"geng");
FileLISTG:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"listg");
FileLISTGtoGAP:=Filename(DirectoriesPackagePrograms("MyPolyhedral"),"LISTGtoGAP");


GRAPE_from_ListEdge:=function(ListEdge)
  local nbVert, GRA, eEdge, i, j;
  nbVert:=Maximum(List(ListEdge, Maximum));
  GRA:=NullGraph(Group(()), nbVert);
  for eEdge in ListEdge
  do
    i:=eEdge[1];
    j:=eEdge[2];
    AddEdgeOrbit(GRA, [i,j]);
    AddEdgeOrbit(GRA, [j,i]);
  od;
  return GRA;
end;


GRAPE_from_ListAdj:=function(ListAdj)
  local nbVert, GRA, iVert, eAdj;
  nbVert:=Length(ListAdj);
  GRA:=NullGraph(Group(()), nbVert);
  for iVert in [1..nbVert]
  do
    for eAdj in ListAdj[iVert]
    do
      AddEdgeOrbit(GRA, [iVert,eAdj]);
    od;
  od;
  return GRA;
end;


AdjacencyMatrixToGRAPE:=function(eMat)
  local nbVert, GRA, iVert, jVert;
  nbVert:=Length(eMat);
  GRA:=NullGraph(Group(()), nbVert);
  for iVert in [1..nbVert]
  do
    for jVert in [1..nbVert]
    do
      if eMat[iVert][jVert]=1 then
        AddEdgeOrbit(GRA, [iVert,jVert]);
      fi;
    od;
  od;
  return GRA;
end;



CheckStrongRegularity:=function(eGR, n, eDeg, lambda, mu)
  local i, j, nbCommonAdj;
  if eGR.order<>n then
    return false;
  fi;
  for i in [1..n]
  do
    if Length(Adjacency(eGR, i))<>eDeg then
      return false;
    fi;
  od;
  for i in [1..n-1]
  do
    for j in [i+1..n]
    do
      nbCommonAdj:=Intersection(Adjacency(eGR, i), Adjacency(eGR, j));
      if IsEdge(eGR, [i,j]) then
        if nbCommonAdj<>lambda then
          return false;
        fi;
      else
        if nbCommonAdj<>mu then
          return false;
        fi;
      fi;
    od;
  od;
  return true;
end;



# some invariant are really to expensive to store
__GetMD5sum:=function(FileName)
  local FileMD5, FileRead, FileProg, TheRet;
  FileMD5:=Filename(POLYHEDRAL_tmpdir, "MD5_out");
  FileRead:=Filename(POLYHEDRAL_tmpdir, "MD5_read");
  FileProg:="md5sum";
  Exec(FileProg, " ", FileName, " > ", FileMD5);
  Exec(FileMD5read, " ", FileMD5, " > ", FileRead);
  TheRet:=ReadAsFunction(FileRead)();
  RemoveFile(FileMD5);
  RemoveFile(FileRead);
  return TheRet;
end;

GetMd5sumObj:=function(eObj)
  local FileInv, eInvMD5;
  FileInv:=Filename(POLYHEDRAL_tmpdir, "eObj5_nd5look");
  SaveDataToFile(FileInv, eObj);
  eInvMD5:=__GetMD5sum(FileInv);
  RemoveFile(FileInv);
  return eInvMD5;
end;


NicePrintOutOfGraph:=function(output, GRA)
  local n, i, eAdj;
  n:=GRA.order;
  AppendTo(output, "n=", n, "\n");
  for i in [1..n]
  do
    AppendTo(output, " ", i, " :");
    for eAdj in Adjacency(GRA, i)
    do
      AppendTo(output, " ", eAdj);
    od;
    AppendTo(output, "\n");
  od;
end;



# use the matrix tree theorem
EnumerateSpanningTrees:=function(TheGRA)
  local nbV, TheLaplacian, eVert, eAdj, TheSubMat;
  nbV:=TheGRA.order;
  TheLaplacian:=NullMat(nbV, nbV);
  for eVert in [1..nbV]
  do
    for eAdj in Adjacency(TheGRA, eVert)
    do
      if eAdj > eVert then
        TheLaplacian[eVert][eVert]:=TheLaplacian[eVert][eVert]+1;
        TheLaplacian[eAdj][eAdj]:=TheLaplacian[eAdj][eAdj]+1;
        TheLaplacian[eAdj][eVert]:=-1;
        TheLaplacian[eVert][eAdj]:=-1;
      fi;
    od;
  od;
  TheSubMat:=List(TheLaplacian{[2..nbV]}, x->x{[2..nbV]});
  return AbsInt(DeterminantMat(TheSubMat));
end;


PrintGraphMyBlissFormat:=function(FileName, TheGRA)
  local nbVert, ListEdges, iVert, eAdj, nbEdge, output, eEdge;
  nbVert:=TheGRA.order;
  ListEdges:=[];
  for iVert in [1..nbVert]
  do
    for eAdj in Adjacency(TheGRA, iVert)
    do
      if eAdj > iVert then
        Add(ListEdges, [iVert, eAdj]);
      fi;
    od;
  od;
  nbEdge:=Length(ListEdges);
  output:=OutputTextFile(FileName, true);
  AppendTo(output, nbVert, " ", nbEdge, "\n");
  for iVert in [1..nbVert]
  do
    AppendTo(output, " 1\n");
  od;
  for eEdge in ListEdges
  do
    AppendTo(output, eEdge[1], " ", eEdge[2], "\n");
  od;
  CloseStream(output);
end;


SAGE_WriteGraph:=function(output, GRA, strName)
  local nbVert, ListEdges, iVert, eAdj, nbEdge, eEdge, IsFirst;
  nbVert:=GRA.order;
  ListEdges:=[];
  for iVert in [1..nbVert]
  do
    for eAdj in Adjacency(GRA, iVert)
    do
      if eAdj > iVert then
        Add(ListEdges, [iVert, eAdj]);
      fi;
    od;
  od;
  nbEdge:=Length(ListEdges);
  AppendTo(output, strName, "=Graph()\n");
  AppendTo(output, strName, ".add_vertices(range(", nbVert, "))\n");
  AppendTo(output, "ListEdges=[");
  IsFirst:=true;
  for eEdge in ListEdges
  do
    if IsFirst=false then
      AppendTo(output, ",");
    fi;
    IsFirst:=false;
    AppendTo(output, "[", eEdge[1]-1, ",", eEdge[2]-1, "]");
  od;
  AppendTo(output, "]\n");
  #
  AppendTo(output, "for iedge in xrange(", nbEdge, "):\n");
  AppendTo(output, "    ", strName, ".add_edge(ListEdges[iedge][0], ListEdges[iedge][1])\n");
end;


SAGE_TestIfHasMinor:=function(G, H)
  local FileInput, FileOutput, output, TheCommand, test;
  FileInput:=Filename(POLYHEDRAL_tmpdir, "TestMinor.sage");
  FileOutput:=Filename(POLYHEDRAL_tmpdir, "TestMinor.out");
  output:=OutputTextFile(FileInput, true);
  SAGE_WriteGraph(output, G, "G");
  SAGE_WriteGraph(output, H, "H");
  AppendTo(output, "try:\n");
  AppendTo(output, "    m=G.minor(H)\n");
  AppendTo(output, "    print \"return true;\"\n");
  AppendTo(output, "except ValueError:\n");
  AppendTo(output, "    print \"return false;\"\n");
  CloseStream(output);
  TheCommand:=Concatenation("sage ", FileInput, " > ", FileOutput);
  Exec(TheCommand);
  test:=ReadAsFunction(FileOutput)();
  RemoveFileIfExist(FileOutput);
  RemoveFileIfExist(FileInput);
  return test;
end;


SAGE_ChromaticNumber:=function(TheGraph)
  local FileInput, FileOutput, output, TheCommand, test;
  FileInput:=Filename(POLYHEDRAL_tmpdir, "TestMinor.sage");
  FileOutput:=Filename(POLYHEDRAL_tmpdir, "TestMinor.out");
  output:=OutputTextFile(FileInput, true);
  AppendTo(output, "from sage.graphs.graph_coloring import vertex_coloring\n");
  SAGE_WriteGraph(output, TheGraph, "TheG");
  AppendTo(output, "eChr = vertex_coloring(TheG, value_only=True)\n");
  AppendTo(output, "print \"return \" + str(eChr) + \";\"");
  CloseStream(output);
  TheCommand:=Concatenation("sage ", FileInput, " > ", FileOutput);
  Exec(TheCommand);
  test:=ReadAsFunction(FileOutput)();
  RemoveFileIfExist(FileOutput);
  RemoveFileIfExist(FileInput);
  return test;
end;









ListSpanningTree:=function(TheGRA)
  local nbVert, ListEdges, eVert, eAdj, nbEdge, ListSolution, ListCompleteSolution, NewListSolution, eSol, NewSol, pos, eEdge, VectorCovering, iVert, iEdge;
  nbVert:=TheGRA.order;
  ListEdges:=[];
  for eVert in [1..nbVert]
  do
    for eAdj in Adjacency(TheGRA, eVert)
    do
      if eAdj > eVert then
        Add(ListEdges, [eVert, eAdj]);
      fi;
    od;
  od;
  nbEdge:=Length(ListEdges);
  ListSolution:=[ListWithIdenticalEntries(nbEdge,0)];
  ListCompleteSolution:=[];
  while(true)
  do
    NewListSolution:=[];
    for eSol in ListSolution
    do
      if Sum(eSol)=0 then
        for eAdj in Adjacency(TheGRA,1)
        do
          eEdge:=[1,eAdj];
          pos:=Position(ListEdges, eEdge);
          NewSol:=ListWithIdenticalEntries(nbEdge,0);
          NewSol[pos]:=1;
          Add(NewListSolution, NewSol);
        od;
      else
        VectorCovering:=ListWithIdenticalEntries(nbVert,0);
        for iEdge in [1..nbEdge]
        do
          if eSol[iEdge]=1 then
            VectorCovering[ListEdges[iEdge]]:=[1,1];
          fi;
        od;
        if Sum(VectorCovering)=nbVert then
          Add(ListCompleteSolution, eSol);
        else
          for eVert in [1..nbVert]
          do
            if VectorCovering[iVert]=1 then
              for eAdj in Adjacency(TheGRA,eVert)
              do
                if VectorCovering[eAdj]=0 then
                  eEdge:=Set([eVert,eAdj]);
                  pos:=Position(ListEdges, eEdge);
                  NewSol:=ShallowCopy(eSol);
                  NewSol[pos]:=1;
                  Add(NewListSolution, NewSol);
                fi;
              od;
            fi;
          od;
        fi;
      fi;
    od;
    ListSolution:=Set(NewListSolution);
  od;
  return rec(ListEdges:=ListEdges, ListSolution:=Set(ListCompleteSolution));
end;



GetMD5expressionOfGraph:=function(ListAdjacency)
  local FileInput, output, nbVert, iVert, eAdj, eStrMD5;
  FileInput:=Filename(POLYHEDRAL_tmpdir, "TheGraph");
  output:=OutputTextFile(FileInput, true);
  nbVert:=Length(ListAdjacency);
  for iVert in [1..nbVert]
  do
    AppendTo(output, "eVert=", iVert, "\n");
    for eAdj in ListAdjacency[iVert]
    do
      AppendTo(output, eAdj, "\n");
    od;
  od;
  CloseStream(output);
  eStrMD5:=__GetMD5sum(FileInput);
  RemoveFile(FileInput);
  return eStrMD5;
end;



__GetGraph6Expression:=function(ListAdj)
  local FileInput, FileOut6, FileRead, FileError, n, output, i, j, TheStr;
  FileInput:=Filename(POLYHEDRAL_tmpdir, "GraphMat");
  FileOut6:=Filename(POLYHEDRAL_tmpdir, "Graph6");
  FileRead:=Filename(POLYHEDRAL_tmpdir, "GraphRead");
  FileError:=Filename(POLYHEDRAL_tmpdir, "GraphError");
  n:=Length(ListAdj);
  output:=OutputTextFile(FileInput, true);
  AppendTo(output, "n=", n, "\n");
  for i in [1..n]
  do
    for j in [1..n]
    do
      if Position(ListAdj[i], j)<>fail then
        AppendTo(output, "1");
      else
        AppendTo(output, "0");
      fi;
    od;
    AppendTo(output, "\n");
  od;
  CloseStream(output);
  Exec(FileAMTOG, " ", FileInput, " > ", FileOut6, " 2>", FileError);
  Exec(FileNautyGraph6Expression, " ", FileOut6, " > ", FileRead);
#  if IsEmptyFile(FileError)=false then
#    Error("Some error happened in GetGraph6Expression");
#  fi;
  TheStr:=ReadAsFunction(FileRead)();
  RemoveFile(FileInput);
  RemoveFile(FileOut6);
  RemoveFile(FileRead);
  RemoveFile(FileError);
  return TheStr;
end;



__SetValue:=function(DistMat)
  local ListSet, n, i, j;
  ListSet:=[];
  n:=Length(DistMat);
  for i in [1..n-1]
  do
    Append(ListSet, DistMat[i]{[i+1..n]});
  od;
  return Set(ListSet);
end;



__SetValue_ScalarMat:=function(ScalarMat)
  local ListSet, n, i, j;
  ListSet:=Set([]);
  n:=Length(ScalarMat);
  for i in [1..n]
  do
    ListSet:=Union(ListSet, Set(ScalarMat[i]{[i..n]}));
  od;
  return ListSet;
end;


GetIsomorphismTypeGraph:=function(n)
  local TheCommand, ListG, FileResult;
  FileResult:=Filename(POLYHEDRAL_tmpdir, "res");
  RemoveFileIfExist(FileResult);
  TheCommand:=Concatenation(FileGENG, " ", String(n), " | ", FileLISTG, " | ", FileLISTGtoGAP, " > ", FileResult);
  Exec(TheCommand);
  ListG:=ReadAsFunction(FileResult)();
  RemoveFileIfExist(FileResult);
  return ListG;
end;


GetIsomorphismTypeGraphSpecEdges:=function(n, nbEdge)
  local TheCommand, ListG, FileResult;
  FileResult:=Filename(POLYHEDRAL_tmpdir, "res");
  RemoveFileIfExist(FileResult);
  TheCommand:=Concatenation(FileGENG, " ", String(n), " ", String(nbEdge), " | ", FileLISTG, " | ", FileLISTGtoGAP, " > ", FileResult);
  Exec(TheCommand);
  ListG:=ReadAsFunction(FileResult)();
  RemoveFileIfExist(FileResult);
  return ListG;
end;


GetIsomorphismTypeGraphOption:=function(n, strOpt)
  local TheCommand, ListG, FileResult;
  FileResult:=Filename(POLYHEDRAL_tmpdir, "res");
  RemoveFileIfExist(FileResult);
  TheCommand:=Concatenation(FileGENG, " ", String(n), " ", strOpt, " | ", FileLISTG, " | ", FileLISTGtoGAP, " > ", FileResult);
  Exec(TheCommand);
  ListG:=ReadAsFunction(FileResult)();
  RemoveFileIfExist(FileResult);
  return ListG;
end;



__PrintPartition:=function(output, ThePartition)
  local nbPart, ThePart, j, i;
  AppendTo(output, "f=[");
  nbPart:=Length(ThePartition);
  for i in [1..nbPart]
  do
    ThePart:=ThePartition[i];
    for j in [1..Length(ThePart)]
    do
      AppendTo(output, ThePart[j]-1);
      if j < Length(ThePart) then
        AppendTo(output, " ");
      fi;
    od;
    if i<nbPart then
      AppendTo(output, "|");
    fi;
  od;
  AppendTo(output, "]\n");
end;


__PrintGraph:=function(output, ListAdjacency)
  local n, i, eV;
  n:=Length(ListAdjacency);
  AppendTo(output, "g\n");
  for i in [1..n]
  do
    AppendTo(output, i-1, " :");
    for eV in ListAdjacency[i]
    do
      AppendTo(output, " ", eV-1);
    od;
    AppendTo(output, ";\n");
  od;
end;

__PrintGraph_Scalable:=function(output, eRecGraph)
  local n, i, eV;
  n:=eRecGraph.n;
  AppendTo(output, "g\n");
  for i in [1..n]
  do
    AppendTo(output, i-1, " :");
    for eV in eRecGraph.GetAdjacent(i)
    do
      AppendTo(output, " ", eV-1);
    od;
    AppendTo(output, ";\n");
  od;
end;




__GetListAdjacency:=function(TheGraph)
  local ListAdjacency, iVert;
  ListAdjacency:=[];
  for iVert in [1..TheGraph.order]
  do
    Add(ListAdjacency, Adjacency(TheGraph, iVert));
  od;
  return ListAdjacency;
end;

SymmetryGroupVertexColoredGraphAdjList:=function(ListAdjacency, ThePartition)
  local FileNauty, FileDR, FileRead, FileError, n, output, TheGroup;
  FileNauty:=Filename(POLYHEDRAL_tmpdir, "GraphInput");
  FileDR:=Filename(POLYHEDRAL_tmpdir, "GraphDRout");
  FileRead:=Filename(POLYHEDRAL_tmpdir, "GraphRead");
  FileError:=Filename(POLYHEDRAL_tmpdir, "GraphError");
  n:=Length(ListAdjacency);
  output:=OutputTextFile(FileNauty, true);
  AppendTo(output, "n=", n, "\n");
  __PrintPartition(output, ThePartition);
  __PrintGraph(output, ListAdjacency);
  AppendTo(output, "x\n");
  CloseStream(output);
  Exec(FileDR2, " < ", FileNauty, " > ", FileDR, " 2>", FileError);
  Exec(FileNautyGroupGAP, " < ", FileDR, " > ", FileRead);
  if IsEmptyFile(FileError)=false then
    Error("Nonempty error file in SymmetryGroupColoredGraph");
  fi;
  TheGroup:=ReadAsFunction(FileRead)();;
#  Print(NullMat(5));
  RemoveFile(FileNauty);
  RemoveFile(FileDR);
  RemoveFile(FileRead);
  RemoveFile(FileError);
  return TheGroup;
end;


SymmetryGroupVertexColoredGraphAdjList_Scalable:=function(eRecGraph)
  local FileNauty, FileDR, FileRead, FileError, n, output, TheGroup;
  FileNauty:=Filename(POLYHEDRAL_tmpdir, "GraphInput");
  FileDR:=Filename(POLYHEDRAL_tmpdir, "GraphDRout");
  FileRead:=Filename(POLYHEDRAL_tmpdir, "GraphRead");
  FileError:=Filename(POLYHEDRAL_tmpdir, "GraphError");
  output:=OutputTextFile(FileNauty, true);
  AppendTo(output, "n=", eRecGraph.n, "\n");
  __PrintPartition(output, eRecGraph.ThePartition);
  __PrintGraph_Scalable(output, eRecGraph);
  AppendTo(output, "x\n");
  CloseStream(output);
  Exec(FileDR2, " < ", FileNauty, " > ", FileDR, " 2>", FileError);
  Exec(FileNautyGroupGAP, " < ", FileDR, " > ", FileRead);
  if IsEmptyFile(FileError)=false then
    Error("Nonempty error file in SymmetryGroupColoredGraph");
  fi;
  TheGroup:=ReadAsFunction(FileRead)();;
#  Print(NullMat(5));
  RemoveFile(FileNauty);
  RemoveFile(FileDR);
  RemoveFile(FileRead);
  RemoveFile(FileError);
  return TheGroup;
end;




SymmetryGroupVertexColoredGraph:=function(TheGraph, ThePartition)
  local ListAdjacency;
  ListAdjacency:=__GetListAdjacency(TheGraph);
  return SymmetryGroupVertexColoredGraphAdjList(ListAdjacency, ThePartition);
end;





CanonicalRepresentativeVertexColoredGraphAdjList:=function(ListAdjacency, ThePartition)
  local FileNauty, FileDR, FileRead, FileError, n, output, CanonicalEList, CanonicalDesc, i, iV, Ladj, kV, DirectImg, ReverseImg, CanonicalList, CanonicalRevList, j;
  FileNauty:=Filename(POLYHEDRAL_tmpdir, "GraphInput");
  FileDR:=Filename(POLYHEDRAL_tmpdir, "GraphDRout");
  FileRead:=Filename(POLYHEDRAL_tmpdir, "GraphRead");
  FileError:=Filename(POLYHEDRAL_tmpdir, "GraphError");
  n:=Length(ListAdjacency);
  output:=OutputTextFile(FileNauty, true);
  AppendTo(output, "n=", n, "\n");
  __PrintPartition(output, ThePartition);
  __PrintGraph(output, ListAdjacency);
  AppendTo(output, "c\n");
  AppendTo(output, "x\n");
  AppendTo(output, "b\n");
  CloseStream(output);
  Exec(FileDR2, " < ", FileNauty, " > ", FileDR, " 2>", FileError);
  Exec(FileNautyReadCanon, " < ", FileDR, " > ", FileRead);
  if IsEmptyFile(FileError)=false then
    Error("Nonempty error file in CanonicalRepresentativeVertexColoredGraphAdjList");
  fi;
  CanonicalEList:=ReadAsFunction(FileRead)();
  CanonicalList:=List(CanonicalEList, x->x+1);
  CanonicalRevList:=ListWithIdenticalEntries(n,0);
  for i in [1..n]
  do
    j:=CanonicalList[i];
    CanonicalRevList[j]:=i;
  od;
  # DirectImg map from canonic to original
  DirectImg:=function(i)
    return CanonicalList[i];
  end;
  ReverseImg:=function(i)
    return CanonicalRevList[i];
  end;
  CanonicalDesc:=[];
  for i in [1..n]
  do
    iV:=DirectImg(i);
    Ladj:=[];
    for kV in ListAdjacency[iV]
    do
      Add(Ladj, ReverseImg(kV));
    od;
    Add(CanonicalDesc, Set(Ladj));
  od;
  RemoveFile(FileNauty);
  RemoveFile(FileDR);
  RemoveFile(FileRead);
  RemoveFile(FileError);
  return rec(CanonicalDesc:=CanonicalDesc,
             CanonicalList:=CanonicalList,
             CanonicalRevList:=CanonicalRevList);
end;

CharacteristicGraphOfSubsetAdjList:=function(ListAdjacency, eCand)
  local nbVert, NewListAdjacency, iVert, ThePartition;
  nbVert:=Length(ListAdjacency);
  NewListAdjacency:=[];
  for iVert in [1..nbVert]
  do
    if Position(eCand, iVert)=fail then
      Add(NewListAdjacency, ListAdjacency[iVert]);
    else
      Add(NewListAdjacency, Concatenation(ListAdjacency[iVert], [nbVert+1]));
    fi;
  od;
  Add(NewListAdjacency, eCand);
  ThePartition:=[[1..nbVert], [nbVert+1]];
  return CanonicalRepresentativeVertexColoredGraphAdjList(NewListAdjacency, ThePartition).CanonicalDesc;
end;


CanonicalRepresentativeVertexColoredGraph:=function(TheGraph, ThePartition)
  local ListAdjacency;
  ListAdjacency:=__GetListAdjacency(TheGraph);
  return CanonicalRepresentativeVertexColoredGraphAdjList(ListAdjacency, ThePartition);
end;



EquivalenceVertexColoredGraphAdjList:=function(ListAdjacency1, ListAdjacency2, ThePartition)
  local FileNauty, FileDR, FileRead, FileError, n, output, TheReply;
  FileNauty:=Filename(POLYHEDRAL_tmpdir, "GraphInput");
  FileDR:=Filename(POLYHEDRAL_tmpdir, "GraphDRout");
  FileRead:=Filename(POLYHEDRAL_tmpdir, "GraphRead");
  FileError:=Filename(POLYHEDRAL_tmpdir, "GraphError");
  n:=Length(ListAdjacency1);
  if n<>Length(ListAdjacency2) then
    return false;
  fi;
  output:=OutputTextFile(FileNauty, true);
  AppendTo(output, "n=", n, "\n");
  __PrintPartition(output, ThePartition);
  __PrintGraph(output, ListAdjacency1);
  AppendTo(output, "c x @\n");
  __PrintGraph(output, ListAdjacency2);
  AppendTo(output, "x ##\n");
  CloseStream(output);
  Exec(FileDR2, " < ", FileNauty, " > ", FileDR, " 2>", FileError);
  Exec(FileNautyIsoOutputGAP, " ", FileDR, " > ", FileRead);
  if IsEmptyFile(FileError)=false then
    Error("Error in EquivalenceVertexColoredGraphAdjList");
  fi;
  TheReply:=ReadAsFunction(FileRead)();
  RemoveFile(FileNauty);
  RemoveFile(FileDR);
  RemoveFile(FileRead);
  RemoveFile(FileError);
  return TheReply;
end;


EquivalenceVertexColoredGraphAdjList_Scalable:=function(eRecGraph1, eRecGraph2)
  local FileNauty, FileDR, FileRead, FileError, n, output, TheReply;
  FileNauty:=Filename(POLYHEDRAL_tmpdir, "GraphInput");
  FileDR:=Filename(POLYHEDRAL_tmpdir, "GraphDRout");
  FileRead:=Filename(POLYHEDRAL_tmpdir, "GraphRead");
  FileError:=Filename(POLYHEDRAL_tmpdir, "GraphError");
  n:=eRecGraph1.n;
  output:=OutputTextFile(FileNauty, true);
  AppendTo(output, "n=", n, "\n");
  __PrintPartition(output, eRecGraph1.ThePartition);
  __PrintGraph_Scalable(output, eRecGraph1);
  AppendTo(output, "c x @\n");
  __PrintGraph_Scalable(output, eRecGraph2);
  AppendTo(output, "x ##\n");
  CloseStream(output);
  Exec(FileDR2, " < ", FileNauty, " > ", FileDR, " 2>", FileError);
  Exec(FileNautyIsoOutputGAP, " ", FileDR, " > ", FileRead);
  if IsEmptyFile(FileError)=false then
    Error("Error in EquivalenceVertexColoredGraphAdjList_Scalable");
  fi;
  TheReply:=ReadAsFunction(FileRead)();
  RemoveFile(FileNauty);
  RemoveFile(FileDR);
  RemoveFile(FileRead);
  RemoveFile(FileError);
  return TheReply;
end;


EquivalenceVertexColoredGraph:=function(TheGraph1, TheGraph2, ThePartition)
  local ListAdjacency1, ListAdjacency2;
  ListAdjacency1:=__GetListAdjacency(TheGraph1);
  ListAdjacency2:=__GetListAdjacency(TheGraph2);
  return EquivalenceVertexColoredGraphAdjList(ListAdjacency1, ListAdjacency2, ThePartition);
end;





__Method4FindTheK:=function(korig)
  local k;
  k:=1;
  while(true)
  do
    if korig < 2^k then
      break;
    fi;
    k:=k+1;
  od;
  return k;
end;

__Method4Partition:=function(korig, n)
  local k;
  k:=__Method4FindTheK(korig);
  return List([1..k], x->[n*(x-1)+1..n*(x-1)+n]);
end;


# this procedure Build the Set:  Seto x Seto x .... x Seto
BuildSet:=function(n, Seto)
  local DO, i, iCol, U, V,C, eVal;
  DO:=[[]];
  for iCol in [1..n]
  do
    C:=ShallowCopy(DO);
    DO:=ShallowCopy([]);
    for i in [1..Length(C)]
    do
      for eVal in Seto
      do
        U:=ShallowCopy(C[i]);
        Add(U, eVal);
        Add(DO, U);
      od;
    od;
  od;
  return DO;
end;



Method4modelEdgeColoredGraph:=function(DistMat, SetV)
  local korig, k, List01Sets, n, ListAdjacency, iVert, i, j, iColor, eVal, jVert, iCol;
  korig:=Length(SetV);
  k:=__Method4FindTheK(korig);
  List01Sets:=BuildSet(k, [0,1]);
  n:=Length(DistMat);
  ListAdjacency:=[];
  for i in [1..k*n]
  do
    Add(ListAdjacency, []);
  od;
  for iVert in [1..n]
  do
    for i in [1..k-1]
    do
      for j in [i+1..k]
      do
        Add(ListAdjacency[n*(i-1)+iVert], n*(j-1)+iVert);
        Add(ListAdjacency[n*(j-1)+iVert], n*(i-1)+iVert);
      od;
    od;
  od;
  for iColor in [1..Length(SetV)]
  do
    eVal:=SetV[iColor];
    for iVert in [1..n-1]
    do
      for jVert in [iVert+1..n]
      do
        if DistMat[iVert][jVert]=eVal then
          for iCol in [1..k]
          do
            if List01Sets[iColor][iCol]=1 then
              Add(ListAdjacency[n*(iCol-1)+iVert], n*(iCol-1)+jVert);
              Add(ListAdjacency[n*(iCol-1)+jVert], n*(iCol-1)+iVert);
            fi;
          od;
        fi;
      od;
    od;
  od;
  return ListAdjacency;
end;


Method4AutomGroupEdgeColoredGraph:=function(DistMat, SetV)
  local TheListAdjacency, ThePartition, korig, n, GRP;
  korig:=Length(SetV);
  n:=Length(DistMat);
  TheListAdjacency:=Method4modelEdgeColoredGraph(DistMat, SetV);
  ThePartition:=__Method4Partition(korig, n);
  GRP:=SymmetryGroupVertexColoredGraphAdjList(TheListAdjacency, ThePartition);
  return SecondReduceGroupAction(GRP, [1..n]);
end;

Method4CanonicalFormEdgeColoredGraph:=function(DistMat, SetV)
  local korig, n, nTot, TheListAdjacency, ThePartition, CanonDesc, CanonicalList, CanonicalRevList, ListI, i, iK, iVert, ListStatus, GetFirstNonAssigned, iCan, jCan, iOrig, jOrig, iOrigBig, iCanBig, DistMatRed, kwork;
  korig:=Length(SetV);
  n:=Length(DistMat);
  TheListAdjacency:=Method4modelEdgeColoredGraph(DistMat, SetV);
  nTot:=Length(TheListAdjacency);
  kwork:=nTot / n;
  ThePartition:=__Method4Partition(korig, n);
  CanonDesc:=CanonicalRepresentativeVertexColoredGraphAdjList(TheListAdjacency, ThePartition);
  # CanonicalList maps canonic to original point.
  CanonicalList:=ListWithIdenticalEntries(n,0);
  CanonicalRevList:=ListWithIdenticalEntries(n,0);
  ListI:=ListWithIdenticalEntries(nTot,1);
  for i in [1..n]
  do
    for iK in [1..kwork]
    do
      iVert:=n*(iK-1) + i;
      ListI[iVert]:=i;
    od;
  od;
  ListStatus:=ListWithIdenticalEntries(nTot,1);
  GetFirstNonAssigned:=function()
    local i;
    for i in [1..nTot]
    do
      if ListStatus[i]=1 then
        return i;
      fi;
    od;
    Error("Problem in GetFirstNonAssigned");
  end;
  for iCan in [1..n]
  do
    iCanBig:=GetFirstNonAssigned();
    iOrigBig:=CanonDesc.CanonicalList[iCanBig];
    iOrig:=ListI[iOrigBig];
    CanonicalList[iCan]:=iOrig;
    CanonicalRevList[iOrig]:=iCan;
    for iK in [1..kwork]
    do
      iOrigBig:=n*(iK-1) + iOrig;
      iCanBig:=CanonDesc.CanonicalRevList[iOrigBig];
      ListStatus[iCanBig]:=0;
    od;
  od;
  DistMatRed:=NullMat(n,n);
  for iCan in [1..n]
  do
    iOrig:=CanonicalList[iCan];
    for jCan in [1..n]
    do
      jOrig:=CanonicalList[jCan];
      DistMatRed[iCan][jCan]:=DistMat[iOrig][jOrig];
    od;
  od;
  return rec(DistMat:=DistMatRed, 
             CanonicalList:=CanonicalList,
             CanonicalRevList:=CanonicalRevList);
end;


Method4CanonicalStringEdgeColoredGraph:=function(DistMat, SetV)
  local korig, n, TheListAdjacency, ThePartition, CanonDesc;
  korig:=Length(SetV);
  n:=Length(DistMat);
  TheListAdjacency:=Method4modelEdgeColoredGraph(DistMat, SetV);
  ThePartition:=__Method4Partition(korig, n);
  CanonDesc:=CanonicalRepresentativeVertexColoredGraphAdjList(TheListAdjacency, ThePartition).CanonicalDesc;
  return __GetGraph6Expression(CanonDesc);
end;





Method4EquivalenceEdgeColoredGraph:=function(DistMat1, DistMat2, SetV)
  local korig, n, TheListAdjacency1, TheListAdjacency2, ThePartition, TheEquiv;
  korig:=Length(SetV);
  n:=Length(DistMat1);
  TheListAdjacency1:=Method4modelEdgeColoredGraph(DistMat1, SetV);
  TheListAdjacency2:=Method4modelEdgeColoredGraph(DistMat2, SetV);
  ThePartition:=__Method4Partition(korig,n);
  TheEquiv:=EquivalenceVertexColoredGraphAdjList(TheListAdjacency1, TheListAdjacency2, ThePartition);
  if TheEquiv=false then
    return false;
  fi;
  return TheEquiv{[1..n]};
end;





Method3EnumerationListSet:=function(n)
  local LSET, i, j, TheSet, ListSets;
  LSET:=[];
  for i in [1..n-1]
  do
    for j in [i+1..n]
    do
      Add(LSET, [i,j]);
    od;
  od;
  ListSets:=[];
  for i in [1..n]
  do
    TheSet:=[];
    for j in [1..n]
    do
      if i<>j then
        Add(TheSet, Position(LSET, Set([i,j])));
      fi;
    od;
    Add(ListSets, Set(TheSet));
  od;
  return ListSets;
end;



AutomorphismGroupEdgeColoredGraph:=function(DistMat)
  local SetV;
  SetV:=__SetValue(DistMat);
  return Method4AutomGroupEdgeColoredGraph(DistMat, SetV);
end;


CanonicalFormEdgeColoredGraph:=function(DistMat)
  local SetV, k, n;
  SetV:=__SetValue(DistMat);
  return Method4CanonicalFormEdgeColoredGraph(DistMat, SetV);
end;



CanonicalStringEdgeColoredGraph:=function(DistMat)
  local SetV, k, n, Meth2_NBV, Meth3_NBV;
  SetV:=__SetValue(DistMat);
  k:=Length(SetV);
  n:=Length(DistMat);
  return rec(Str:=Method4CanonicalStringEdgeColoredGraph(DistMat, SetV), SetV:=SetV);
end;





IsIsomorphicEdgeColoredGraph:=function(DistMat1, DistMat2)
  local SetV, k, n, Meth2_NBV, Meth3_NBV;
  SetV:=__SetValue(DistMat1);
  if __SetValue(DistMat2)<>SetV then
    return false;
  fi;
  k:=Length(SetV);
  n:=Length(DistMat1);
  return Method4EquivalenceEdgeColoredGraph(DistMat1, DistMat2, SetV);
end;


GetFirstSecondVal:=function(SetV)
  local FirstNewVal, SecondNewVal;
  FirstNewVal:=0;
  while(true)
  do
    if Position(SetV, FirstNewVal)=fail then
      break;
    fi;
    FirstNewVal:=FirstNewVal+1;
  od;
  SecondNewVal:=FirstNewVal+1;
  while(true)
  do
    if Position(SetV, SecondNewVal)=fail then
      break;
    fi;
    SecondNewVal:=SecondNewVal+1;
  od;
  return [FirstNewVal, SecondNewVal];
end;

#
# we work in the framework of scalar products
# while the dreadnaut formalism uses distance matrices
# i.e. with 0 on the diagonal. We ought to take care of that
MappedScalarMatrixDistanceMatrix:=function(ScalarMat)
  local DistMat, SetV, eRecN, n, n2, i, j, FirstNewVal, SecondNewVal;
  n:=Length(ScalarMat);
  n2:=n+2;
  SetV:=__SetValue_ScalarMat(ScalarMat);
  eRecN:=GetFirstSecondVal(SetV);
  FirstNewVal:=eRecN[1];
  SecondNewVal:=eRecN[2];
  DistMat:=NullMat(n2, n2);
  for i in [1..n-1]
  do
    for j in [i+1..n]
    do
      DistMat[i][j]:=ScalarMat[i][j];
      DistMat[j][i]:=ScalarMat[i][j];
    od;
  od;
  for i in [1..n]
  do
    DistMat[i][n+1]:=ScalarMat[i][i];
    DistMat[n+1][i]:=ScalarMat[i][i];
    DistMat[i][n+2]:=FirstNewVal;
    DistMat[n+2][i]:=FirstNewVal;
  od;
  DistMat[n+1][n+2]:=SecondNewVal;
  DistMat[n+2][n+1]:=SecondNewVal;
  return DistMat;
end;

GetSetColor_Scalable:=function(eRecScalColor)
  local n, SetV, i, eLine, eRecN;
  SetV:=Set([]);
  n:=eRecScalColor.n;
  for i in [1..n]
  do
#    Print("i=", i, "\n");
    eLine:=eRecScalColor.GetLineColor(i);
    SetV:=Union(SetV, Set(eLine));
  od;
  eRecN:=GetFirstSecondVal(SetV);
  return rec(SetV:=SetV, eRecN:=eRecN);
end;

GetFuncListAdjacentMethod4_Scalable:=function(InfC, eRecScalColor)
  local FirstNewVal, SecondNewVal, korig, k, List01Sets, SetVext, n, n2, nExt, GetLineExtended, GetAdjacent, ThePartition;
  FirstNewVal:=InfC.eRecN[1];
  SecondNewVal:=InfC.eRecN[2];
  korig:=Length(InfC.SetV)+2;
  k:=__Method4FindTheK(korig);
  List01Sets:=BuildSet(k, [0,1]);
  SetVext:=Concatenation(InfC.SetV, InfC.eRecN);
  n:=eRecScalColor.n;
  n2:=n+2;
  nExt:=k*n2;
  ThePartition:=__Method4Partition(korig,n2);
  GetLineExtended:=function(i)
    local eLine;
#    Print("k=", k, " korig=", korig, "\n");
#    Print("n=", n, " nExt=", nExt, "\n");
    if i<=n then
      eLine:=eRecScalColor.GetLineColor(i);
      return Concatenation(eLine{[1..i-1]},[0],eLine{[i+1..n]},[eLine[i],FirstNewVal]);
    fi;
    if i=n+1 then
      return Concatenation(List([1..n],x->eRecScalColor.GetScalarColor(x,x)),[0,SecondNewVal]);
    fi;
    if i=n+2 then
      return Concatenation(ListWithIdenticalEntries(n,FirstNewVal),[SecondNewVal,0]);
    fi;
  end;
  GetAdjacent:=function(iExt)
    local iB, iC, i, kPos, ListAdjacent, iK, eAdj, eLine, j, eColor, iColor;
    iB:=iExt-1;
    iC:=iB mod n2;
    i:=iC+1;
    kPos:=1+(iExt-i)/n2;
    ListAdjacent:=[];
    for iK in [1..k]
    do
      if iK<>kPos then
        eAdj:=i+(iK-1)*n2;
        Add(ListAdjacent, eAdj);
      fi;
    od;
    eLine:=GetLineExtended(i);
    for j in [1..n2]
    do
      if j<>i then
        eColor:=eLine[j];
        iColor:=Position(SetVext, eColor);
        if List01Sets[iColor][kPos]=1 then
          eAdj:=j + (kPos-1)*n2;
          Add(ListAdjacent, eAdj);
        fi;
      fi;
    od;
    return ListAdjacent;
  end;
  return rec(GetAdjacent:=GetAdjacent, n:=nExt, ThePartition:=ThePartition);
end;

AutomorphismGroupColoredGraph_Scalable:=function(eRecScalColor)
  local n, InfC, eRecGraph, GRP, NewListGens, eGen, eList, RetGRP;
  n:=eRecScalColor.n;
  InfC:=GetSetColor_Scalable(eRecScalColor);
  eRecGraph:=GetFuncListAdjacentMethod4_Scalable(InfC, eRecScalColor);
  GRP:=SymmetryGroupVertexColoredGraphAdjList_Scalable(eRecGraph);
  NewListGens:=[];
  for eGen in GeneratorsOfGroup(GRP)
  do
    eList:=List([1..n], x->OnPoints(x, eGen));
    Add(NewListGens, PermList(eList));
  od;
  RetGRP:=Group(NewListGens);
  SetSize(RetGRP, Order(GRP));
  return RetGRP;
end;

AutomorphismGroupColoredGraph:=function(ScalarMat)
  local DistMat, NewListGens, GRP, eGen, eList, RetGRP;
  DistMat:=MappedScalarMatrixDistanceMatrix(ScalarMat);
  NewListGens:=[];
  GRP:=AutomorphismGroupEdgeColoredGraph(DistMat);
  for eGen in GeneratorsOfGroup(GRP)
  do
    eList:=List([1..Length(ScalarMat)], x->OnPoints(x, eGen));
    Add(NewListGens, PermList(eList));
  od;
  RetGRP:=Group(NewListGens);
  SetSize(RetGRP, Order(GRP));
  return RetGRP;
end;

IsIsomorphicColoredGraph_Scalable:=function(eRecScalColor1, eRecScalColor2)
  local n, InfC, eRecGraph1, eRecGraph2, test;
  n:=eRecScalColor1.n;
  if n<>eRecScalColor2.n then
    return false;
  fi;
  InfC:=GetSetColor_Scalable(eRecScalColor1);
  if InfC<>GetSetColor_Scalable(eRecScalColor2) then
    return false;
  fi;
  eRecGraph1:=GetFuncListAdjacentMethod4_Scalable(InfC, eRecScalColor1);
  eRecGraph2:=GetFuncListAdjacentMethod4_Scalable(InfC, eRecScalColor2);
  test:=EquivalenceVertexColoredGraphAdjList_Scalable(eRecGraph1, eRecGraph2);
  if test=false then
    return false;
  else
    return test{[1..n]};
  fi;
end;


IsIsomorphicColoredGraph:=function(ScalarMat1, ScalarMat2)
  local DistMat1, DistMat2, test;
  DistMat1:=MappedScalarMatrixDistanceMatrix(ScalarMat1);
  DistMat2:=MappedScalarMatrixDistanceMatrix(ScalarMat2);
  test:=IsIsomorphicEdgeColoredGraph(DistMat1, DistMat2);
  if test=false then
    return false;
  else
    return test{[1..Length(ScalarMat1)]};
  fi;
end;

CanonicalFormColoredGraph:=function(ScalarMat)
  local n, DistMat, CanonDesc, CanonicalList, CanonicalRevList, ListStatus, iOrigBig, iCanBig, GetFirstNonAssigned, iCan, iOrig, ScalarMatCan, jCan, jOrig;
  n:=Length(ScalarMat);
  DistMat:=MappedScalarMatrixDistanceMatrix(ScalarMat);
  CanonDesc:=CanonicalFormEdgeColoredGraph(DistMat);
  CanonicalList:=ListWithIdenticalEntries(n,0);
  CanonicalRevList:=ListWithIdenticalEntries(n,0);
  ListStatus:=ListWithIdenticalEntries(n+2,1);
  for iOrigBig in [n+1..n+2]
  do
    iCanBig:=CanonDesc.CanonicalRevList[iOrigBig];
    ListStatus[iCanBig]:=0;
  od;
  GetFirstNonAssigned:=function()
    local iCanBig;
    for iCanBig in [1..n+2]
    do
      if ListStatus[iCanBig]=1 then
        return iCanBig;
      fi;
    od;
    Error("Problem in CanonicalFormColoredGraph");
  end;
  for iCan in [1..n]
  do
    iCanBig:=GetFirstNonAssigned();
    iOrig:=CanonDesc.CanonicalList[iCanBig];
    CanonicalList[iCan]:=iOrig;
    CanonicalRevList[iOrig]:=iCan;
    ListStatus[iCanBig]:=0;
  od;
  ScalarMatCan:=NullMat(n,n);
  for iCan in [1..n]
  do
    iOrig:=CanonicalList[iCan];
    for jCan in [1..n]
    do
      jOrig:=CanonicalList[jCan];
      ScalarMatCan[iCan][jCan]:=ScalarMat[iOrig][jOrig];
    od;
  od;
  return rec(ScalarMat:=ScalarMatCan,
             CanonicalList:=CanonicalList,
             CanonicalRevList:=CanonicalRevList);
end;




GetNewValues:=function(SetV, nbNew)
  local iNew, ListNewValue, eNewValue;
  ListNewValue:=[];
  eNewValue:=0;
  for iNew in [1..nbNew]
  do
    eNewValue:=eNewValue+1;
    while(true)
    do
      if Position(SetV, eNewValue)=fail then
        break;
      fi;
      eNewValue:=eNewValue+1;
    od;
    Add(ListNewValue, eNewValue);
  od;
  return ListNewValue;
end;



MappedWeightedDigraphToWeightedSymmetricDigraph:=function(ScalarMat)
  local DistMat, SetV, n, n2, i, j, FirstNewVal, SecondNewVal, eVal, nbNew, ListNewValue;
  n:=Length(ScalarMat);
  SetV:=__SetValue_ScalarMat(ScalarMat);
  nbNew:=3;
  ListNewValue:=GetNewValues(SetV, nbNew);
#  Print("ListNewValue=", ListNewValue, "\n");
  #
  # Now reating the matrix
  #
  DistMat:=NullMat(2*n, 2*n);
  for i in [1..n]
  do
    for j in [1..n]
    do
      if i<>j then
        DistMat[i][j]:=ListNewValue[1];
        DistMat[j][i]:=ListNewValue[1];
        DistMat[i+n][j+n]:=ListNewValue[2];
        DistMat[j+n][i+n]:=ListNewValue[2];
      fi;
    od;
  od;
  for i in [1..n]
  do
    eVal:=ScalarMat[i][i];
    DistMat[i][i]:=eVal;
    DistMat[i+n][i+n]:=eVal;
  od;
  for i in [1..n]
  do
    DistMat[i][i+n]:=ListNewValue[3];
    DistMat[i+n][i]:=ListNewValue[3];
  od;
  for i in [1..n]
  do
    for j in [1..n]
    do
      if i<>j then
        eVal:=ScalarMat[i][j];
        DistMat[i][j+n]:=eVal;
        DistMat[j+n][i]:=eVal;
      fi;
    od;
  od;
  return DistMat;
end;



AutomorphismWeightedDigraph:=function(ScalarMat)
  local n, DistMat, NewListGens, GRP, eGen, eList, RetGRP;
  n:=Length(ScalarMat);
  DistMat:=MappedWeightedDigraphToWeightedSymmetricDigraph(ScalarMat);
  NewListGens:=[];
  GRP:=AutomorphismGroupColoredGraph(DistMat);
  for eGen in GeneratorsOfGroup(GRP)
  do
    eList:=List([1..n], x->OnPoints(x, eGen));
    Add(NewListGens, PermList(eList));
  od;
  RetGRP:=Group(NewListGens);
  SetSize(RetGRP, Order(GRP));
  return RetGRP;
end;


IsIsomorphicWeightDigraph:=function(ScalarMat1, ScalarMat2)
  local n, DistMat1, DistMat2, test;
  n:=Length(ScalarMat1);
  DistMat1:=MappedWeightedDigraphToWeightedSymmetricDigraph(ScalarMat1);
  DistMat2:=MappedWeightedDigraphToWeightedSymmetricDigraph(ScalarMat2);
  test:=IsIsomorphicColoredGraph(DistMat1, DistMat2);
  if test=false then
    return false;
  else
    return test{[1..n]};
  fi;
end;

GetConnectedComponentsListAdj:=function(ListAdjacency)
  local nbVert, ListActive, ListColor, nbColor, IsFinished, iVert, IsFinished2, jVert, eAdj;
  nbVert:=Length(ListAdjacency);
  ListActive:=ListWithIdenticalEntries(nbVert,0);
  ListColor:=ListWithIdenticalEntries(nbVert,0);
  nbColor:=0;
  while(true)
  do
    IsFinished:=true;
    for iVert in [1..nbVert]
    do
      if ListColor[iVert]=0 then
        nbColor:=nbColor+1;
        IsFinished:=false;
        ListColor[iVert]:=nbColor;
        ListActive[iVert]:=1;
        while(true)
        do
          IsFinished2:=true;
          for jVert in [1..nbVert]
          do
            if ListActive[jVert]=1 then
              ListActive[jVert]:=0;
              IsFinished2:=false;
              for eAdj in ListAdjacency[jVert]
              do
                if ListColor[eAdj]>0 then
                  if ListColor[eAdj]<>nbColor then
                    Error("Bug found, please debug");
                  fi;
                else
                  ListColor[eAdj]:=nbColor;
                  ListActive[eAdj]:=1;
                fi;
              od;
            fi;
          od;
          if IsFinished2=true then
            break;
          fi;
        od;
      fi;
    od;
    if IsFinished=true then
      break;
    fi;
  od;
  return ListColor;
end;

GetBipartitionConnected:=function(GR)
  local nbDone, nbV, TheVectorStatus, TheVectorDone, iVert, eVert, AdjStat;
  nbDone:=0;
  nbV:=GR.order;
  TheVectorStatus:=ListWithIdenticalEntries(nbV, 0);
  TheVectorDone:=ListWithIdenticalEntries(nbV, 0);
  TheVectorStatus[1]:=1;
  while(true)
  do
    for iVert in [1..nbV]
    do
      if TheVectorDone[iVert]=0 and TheVectorStatus[iVert]>0 then
        TheVectorDone[iVert]:=1;
        nbDone:=nbDone+1;
        AdjStat:=3-TheVectorStatus[iVert];
        for eVert in Adjacency(GR, iVert)
        do
          if TheVectorStatus[eVert]>0 and TheVectorStatus[eVert]<>AdjStat then
            Error("You try to get bipartition of a non-bipartite graph");
          fi;
          TheVectorStatus[eVert]:=AdjStat;
        od;
      fi;
    od;
    if nbDone=nbV then
      break;
    fi;
  od;
  return TheVectorStatus;
end;

GetBipartition:=function(GR)
  local LConn, nbVert, ListStatus, eConn, GRred, i, j, TheVect;
  LConn:=ConnectedComponents(GR);
  nbVert:=GR.order;
  ListStatus:=ListWithIdenticalEntries(nbVert, 0);
  for eConn in LConn
  do
    GRred:=NullGraph(Group(()), Length(eConn));
    for i in [1..Length(eConn)-1]
    do
      for j in [i+1..Length(eConn)]
      do
        if IsEdge(GR, [eConn[i], eConn[j]])=true then
          AddEdgeOrbit(GRred, [i, j]);
          AddEdgeOrbit(GRred, [j, i]);
        fi;
      od;
    od;
    TheVect:=GetBipartitionConnected(GRred);
    for i in [1..Length(eConn)]
    do
      ListStatus[eConn[i]]:=TheVect[i];
    od;
  od;
  return ListStatus;
end;




FindShortestPath:=function(Gra, x, y)
  local FuncNextVert, Dist, ePath, CurrentVert;
  FuncNextVert:=function(VVert, d)
    local u;
    for u in Adjacency(Gra, VVert)
    do
      if Distance(Gra, u, y)=d-1 then
        return u;
      fi;
    od;
  end;
  Dist:=Distance(Gra, x, y);
  if Dist=-1 then
    Error("Cannot find shortest path when vertices are not connected");
  fi;
  ePath:=[x];
  CurrentVert:=x;
  while(Dist>0)
  do
    CurrentVert:=FuncNextVert(CurrentVert, Dist);
    Add(ePath, CurrentVert);
    Dist:=Dist-1;
  od;
  return ePath;
end;


FindAllShortestPath:=function(Gra, x, y)
  local Dist, ListPath, NewListPath, iPath, ePath, fPath, i, u, CurrentVert, Ladj;
  Dist:=Distance(Gra, x, y);
  ListPath:=[[x]];
  for i in [1..Dist]
  do
    NewListPath:=[];
    for ePath in ListPath
    do
      CurrentVert:=ePath[Length(ePath)];
      Ladj:=Adjacency(Gra, CurrentVert);
#      Print("|Ladj|=", Length(Ladj), "\n");
      for u in Ladj
      do
        if Distance(Gra, u, y)=Dist - i then
#          Print("  u=", u, "\n");
          fPath:=Concatenation(ePath, [u]);
          Add(NewListPath, fPath);
        fi;
      od;
    od;
#    Print("NewListPath=", NewListPath, "\n");
    ListPath:=ShallowCopy(NewListPath);
  od;
  return ListPath;
end;


IsUnionOfCycle:=function(Gra)
  local nbVert, iVert, Ladj, eAdj;
  nbVert:=Gra.order;
  for iVert in [1..nbVert]
  do
    Ladj:=Adjacency(Gra, iVert);
    if Length(Ladj)=1 then
      eAdj:=Ladj[1];
      if Length(Adjacency(Gra, eAdj))<>1 then
        return false;
      fi;
    else
      if Length(Ladj)<>2 then
        return false;
      fi;
    fi;
  od;
  return true;
end;


FindMaximalCycles:=function(GRA)
  local n, ListMaximalCycle, i, ListConf, NewListConf, eConf, NewConf, eFirst, eLast, LAdj, eAdj;
  n:=GRA.order;
  ListMaximalCycle:=[];
  for i in [1..n]
  do
    ListConf:=[[1]];
    while(true)
    do
      NewListConf:=[];
      for eConf in ListConf
      do
        eFirst:=eConf[1];
        eLast:=eConf[Length(eConf)];
        LAdj:=Adjacency(GRA, eLast);
        if Position(LAdj, eFirst)<>fail and Length(eConf)>2 then
	  Add(ListMaximalCycle, eConf);
	fi;
	for eAdj in LAdj
	do
	  if Position(eConf, eAdj)=fail then
	    NewConf:=Concatenation(eConf, [eAdj]);
	    Add(NewListConf, NewConf);
	  fi;
	od;
      od;
      if Length(NewListConf)=0 then
        break;
      fi;
      ListConf:=NewListConf;
    od;
  od;
  return ListMaximalCycle;
end;





FindAllShortestCycles:=function(Gra)
  local ListCycle, i, u, GraNew, eAdj, Ladj, FuncInsert;
  ListCycle:=[];
  FuncInsert:=function(u)
    AddSet(ListCycle, DihedralCanonicalization(u));
  end;
  for i in [1..Gra.order-1]
  do
    Ladj:=Adjacency(Gra, i);
    if Length(Ladj)=1 then
      FuncInsert([i, Ladj[1]]);
    else
      for eAdj in Ladj
      do
        if eAdj>i then
          GraNew:=StructuralCopy(Gra);
          RemoveEdgeOrbit(GraNew, [i,eAdj]);
          RemoveEdgeOrbit(GraNew, [eAdj,i]);
          for u in FindAllShortestPath(GraNew, i, eAdj)
          do
            FuncInsert(u);
          od;
        fi;
      od;
    fi;
  od;
  return ListCycle;
end;


GRAPH_CompleteGraph:=function(n)
  local GRA, i, j;
  GRA:=NullGraph(Group(()), n);
  for i in [1..n-1]
  do
    for j in [i+1..n]
    do
      AddEdgeOrbit(GRA, [i,j]);
      AddEdgeOrbit(GRA, [j,i]);
    od;
  od;
  return GRA;
end;

GRAPH_JohnsonGraph:=function(n, s)
  local LSet, nbSet, GRA, iSet, jSet, eInt;
  LSet:=Combinations([1..n],s);
  nbSet:=Length(LSet);
  GRA:=NullGraph(Group(()), nbSet);
  for iSet in [1..nbSet-1]
  do
    for jSet in [iSet+1..nbSet]
    do
      eInt:=Intersection(LSet[iSet], LSet[jSet]);
      if Length(eInt)=s-1 then
        AddEdgeOrbit(GRA, [iSet,jSet]);
        AddEdgeOrbit(GRA, [jSet,iSet]);
      fi;
    od;
  od;
  return GRA;
end;


# --- GRAPH_EnumerateCycles is for enumerating cycles in the graph TheGRA with symmetry GRP
# --- RecOpt is a record containing the requirement of the enumeration
#    --- RequireIsometricCycleFixedLength for having isometric cycles of fixed length
#    --- RequireIrreducible of cycles for avoiding cycles that can be decomposed.
#    --- TheLen being the length of the isometric cycles considered (if that option is selected obviously)
#    --- UseMinimumOrbit for having
GRAPH_EnumerateCycles:=function(TheGRA, GRPvert, RecOpt)
  local nbVert, O, ListOrb, iK, NewListOrb, FuncInsert, eOrb, eVert, fOrb, ePerm1, ePerm2, DihedGrp, Canonicalize, GetTheCompleteOrbit, GetTotal, FinalListOrb, CycleDistance, IsIsometricCycle, TheDiff, FuncInsertFinal, ListListAdj, ListEdge, LAdj, IndexMatrix, GetEdgeSet, fVert, nbEdge, eEdge, iEdge, pos, ListPermEdge, eGen, eList, eEdgeImg, IsExtensibleIrreducible, IsClosed, GRPedge, IsFinalIrreducible, IsCorrectFinal, IsCorrectEnum, TestEquivalenceFullCycle, IsIsometricCycle_General, IsIsometricCycleFixedLength, IsExtendibleIrreducible, testClosed, UseMinimumOrbit;
  nbVert:=TheGRA.order;
  ListListAdj:=[];
  ListEdge:=[];
  for eVert in [1..nbVert]
  do
    LAdj:=Set(Adjacency(TheGRA, eVert));
    Add(ListListAdj, LAdj);
    for fVert in LAdj
    do
      if fVert > eVert then
        Add(ListEdge, [eVert, fVert]);
      fi;
    od;
  od;
  nbEdge:=Length(ListEdge);
  IndexMatrix:=NullMat(nbVert, nbVert);
  for iEdge in [1..nbEdge]
  do
    eEdge:=ListEdge[iEdge];
    IndexMatrix[eEdge[1]][eEdge[2]]:=iEdge;
    IndexMatrix[eEdge[2]][eEdge[1]]:=iEdge;
  od;
  ListPermEdge:=[];
  for eGen in GeneratorsOfGroup(GRPvert)
  do
    eList:=[];
    for eEdge in ListEdge
    do
      eEdgeImg:=OnSets(eEdge, eGen);
      pos:=Position(ListEdge, eEdgeImg);
      Add(eList, pos);
    od;
    Add(ListPermEdge, PermList(eList));
  od;
  GRPedge:=Group(ListPermEdge);
  GetEdgeSet:=function(eCycleVert)
    local eListEdge, len, i, j, eVert, fVert, idx;
    len:=Length(eCycleVert);
    eListEdge:=ListWithIdenticalEntries(len,0);
    for i in [1..len]
    do
      j:=NextIdx(len,i);
      eVert:=eCycleVert[i];
      fVert:=eCycleVert[j];
      idx:=IndexMatrix[eVert][fVert];
      if idx=0 then
        Error("logical problem");
      fi;
      eListEdge[i]:=idx;
    od;
    return eListEdge;
  end;
  TestEquivalenceFullCycle:=function(eList1, eList2)
    local eListEdge1, eListEdge2;
    eListEdge1:=GetEdgeSet(eList1);
    eListEdge2:=GetEdgeSet(eList2);
    return RepresentativeAction(GRPedge, eListEdge1, eListEdge2, OnSets);
  end;
  O:=Orbits(GRPvert, [1..nbVert], OnPoints);
  Print("iK=1 |O|=", Length(O), "\n");
  ListOrb:=List(O, x->[x[1]]);
  CycleDistance:=function(i,j, eLen)
    return Minimum(j-i, eLen-(j-i));
  end;
  IsIsometricCycle_General:=function(eOrb, eLen)
    local len, i, j, eVert, fVert, dist;
    len:=Length(eOrb);
    for i in [1..len-1]
    do
      for j in [i+1..len]
      do
        eVert:=eOrb[i];
        fVert:=eOrb[j];
        dist:=CycleDistance(i,j, eLen);
        if dist<>Distance(TheGRA, eVert, fVert) then
          return false;
        fi;
      od;
    od;
    return true;
  end;
  IsIsometricCycleFixedLength:=function(eOrb)
    return IsIsometricCycle_General(eOrb, RecOpt.TheLen);
  end;
  IsIsometricCycle:=function(eOrb)
    return IsIsometricCycle_General(eOrb, Length(eOrb));
  end;
  IsClosed:=function(eList)
    local len, eFirst, eLast, idx;
    len:=Length(eList);
    eFirst:=eList[1];
    eLast:=eList[len];
    idx:=IndexMatrix[eFirst][eLast];
    if idx=0 then
      return false;
    fi;
    return true;
  end;
  IsExtendibleIrreducible:=function(eList)
    local len, TheCrit, TheInt, eLast;
    len:=Length(eList);
    TheCrit:=Set(eList{[2..len-2]});
    eLast:=eList[len];
    TheInt:=Intersection(ListListAdj[eLast], TheCrit);
    if Length(TheInt)>0 then
      return false;
    fi;
    return true;
  end;
  IsFinalIrreducible:=function(eList)
    local len, i, iNext, iPrev, eVert, eVertNext, eVertPrev, TheInt, TheDiff;
    if IsClosed(eList)=false then
      return false;
    fi;
    if Length(eList)=2 then
      return false;
    fi;
    len:=Length(eList);
    for i in [1..len]
    do
      iNext:=NextIdx(len,i);
      iPrev:=PrevIdx(len,i);
      eVert:=eList[i];
      eVertNext:=eList[iNext];
      eVertPrev:=eList[iPrev];
      TheInt:=Intersection(ListListAdj[eVert], Set(eList));
      if Position(TheInt, eVertNext)=fail then
        Error("logical error 1");
      fi;
      if Position(TheInt, eVertPrev)=fail then
        Error("logical error 2");
      fi;
      TheDiff:=Difference(TheInt, Set([eVertNext, eVertPrev]));
      if Length(TheDiff)>0 then
        return false;
      fi;
    od;
    return true;
  end;
  FinalListOrb:=[];
  FuncInsertFinal:=function(eOrb)
    local fOrb, test;
    for fOrb in FinalListOrb
    do
      test:=TestEquivalenceFullCycle(eOrb, fOrb);
      if test<>fail then
        return;
      fi;
    od;
    Add(FinalListOrb, eOrb);
  end;
  iK:=2;
  while(true)
  do
    NewListOrb:=[];
    FuncInsert:=function(eOrb)
      local eOrbMin, fOrb;
      if RecOpt.UseMinimumOrbit then
        eOrbMin:=Minimum(Orbit(GRPvert, eOrb, OnTuples));
	if Position(NewListOrb, eOrbMin)<>fail then
	  return;
	fi;
	Add(NewListOrb, eOrbMin);
      else
        for fOrb in NewListOrb
        do
          if RepresentativeAction(GRPvert, eOrb, fOrb, OnTuples)<>fail then
            return;
          fi;
        od;
        Add(NewListOrb, eOrb);
      fi;
    end;
    for eOrb in ListOrb
    do
      TheDiff:=Difference(ListListAdj[eOrb[iK-1]], Set(eOrb));
      for eVert in TheDiff
      do
        fOrb:=Concatenation(eOrb, [eVert]);
        testClosed:=IsClosed(fOrb);
        IsCorrectEnum:=true;
        if RecOpt.RequireIsometricCycleFixedLength then
          IsCorrectEnum:=IsIsometricCycleFixedLength(fOrb);
        fi;
        if RecOpt.RequireIsometric then
          IsCorrectEnum:=IsIsometricCycleFixedLength(fOrb);
        fi;
        if RecOpt.RequireIrreducible then
          IsCorrectEnum:=IsExtendibleIrreducible(fOrb);
        fi;
        IsCorrectFinal:=testClosed;
        if IsCorrectFinal and RecOpt.RequireIsometric then
          IsCorrectFinal:=IsIsometricCycle(fOrb);
        fi;
        if IsCorrectFinal and RecOpt.RequireIrreducible then
          IsCorrectFinal:=IsFinalIrreducible(fOrb);
        fi;
        if IsCorrectEnum then
          FuncInsert(fOrb);
        fi;
        if IsCorrectFinal then
          FuncInsertFinal(fOrb);
        fi;
      od;
    od;
    Print("iK=", iK, " |NewListOrb|=", Length(NewListOrb), " |FinalListOrb|=", Length(FinalListOrb), "\n");
    iK:=iK+1;
    if Length(NewListOrb)=0 then
      break;
    fi;
    ListOrb:=ShallowCopy(NewListOrb);
  od;
  Print("|FinalListOrb|=", Length(FinalListOrb), "\n");
  Canonicalize:=function(eCycle)
    return Minimum(Orbit(DihedGrp, eCycle, Permuted));
  end;
  GetTheCompleteOrbit:=function(eOrb)
    local ListStatus, TheOrbit, FuncInsert, IsFinished, i, eGen, eImgCycle;
    ListStatus:=[];
    TheOrbit:=[];
    FuncInsert:=function(eCycle)
      local TheCanCycle;
      TheCanCycle:=Canonicalize(eCycle);
      if Position(TheOrbit, TheCanCycle)<>fail then
        return;
      fi;
      Add(TheOrbit, TheCanCycle);
      Add(ListStatus, 0);
    end;
    FuncInsert(eOrb);
    while(true)
    do
      IsFinished:=true;
      for i in [1..Length(TheOrbit)]
      do
        if ListStatus[i]=0 then
          ListStatus[i]:=1;
          IsFinished:=false;
          for eGen in GeneratorsOfGroup(GRPvert)
          do
            eImgCycle:=OnTuples(TheOrbit[i], eGen);
            FuncInsert(eImgCycle);
          od;
        fi;
      od;
      if IsFinished=true then
        break;
      fi;
    od;
#    Print("|TheOrbit|=", Length(TheOrbit), "\n");
    return TheOrbit;
  end;
  GetTotal:=function()
    local TotalList, eOrb;
    TotalList:=[];
    for eOrb in FinalListOrb
    do
      Append(TotalList, GetTheCompleteOrbit(eOrb));
    od;
    return TotalList;
  end;
  return rec(FinalListOrb:=FinalListOrb, GetTheCompleteOrbit:=GetTheCompleteOrbit, GetTotal:=GetTotal);
end;

BreadthFirstSearchReordering:=function(GRAin)
  local nbVert, ListCorresp, ListCorrespRev, ListActive, IsFinished, nbNeighUnresolved, eVertSelect, eVert, nbUnres, idx, eAdj, eVertNew, eVertOld, eAdjNew, eAdjOld, GRAreturn, test;
  nbVert:=GRAin.order;
  ListCorresp:=ListWithIdenticalEntries(nbVert, 0);
  ListCorrespRev:=ListWithIdenticalEntries(nbVert, 0);
  ListActive:=ListWithIdenticalEntries(nbVert, 0);
  ListActive[1]:=1;
  ListCorresp[1]:=1;
  ListCorrespRev[1]:=1;
  idx:=1;
  while(true)
  do
    IsFinished:=true;
    nbNeighUnresolved:=nbVert+3;
    eVertSelect:=-1;
    for eVert in [1..nbVert]
    do
      if ListActive[eVert]=1 then
        IsFinished:=false;
        nbUnres:=0;
        for eAdj in Adjacency(GRAin, eVert)
        do
          if ListCorrespRev[eAdj]=0 then
            nbUnres:=nbUnres+1;
          fi;
        od;
        if nbUnres<nbNeighUnresolved then
          nbNeighUnresolved:=nbUnres;
          eVertSelect:=eVert;
        fi;
      fi;
    od;
    if IsFinished=true then
      break;
    fi;
    ListActive[eVertSelect]:=0;
    for eAdj in Adjacency(GRAin, eVertSelect)
    do
      if ListCorrespRev[eAdj]=0 then
        idx:=idx+1;
        ListCorresp[idx]:=eAdj;
        ListCorrespRev[eAdj]:=idx;
        ListActive[eAdj]:=1;
      fi;
    od;
  od;
  GRAreturn:=NullGraph(Group(()), nbVert);
  for eVertNew in [1..nbVert]
  do
    eVertOld:=ListCorresp[eVertNew];
    for eAdjOld in Adjacency(GRAin, eVertOld)
    do
      eAdjNew:=ListCorrespRev[eAdjOld];
      AddEdgeOrbit(GRAreturn, [eVertNew, eAdjNew]);
    od;
  od;
  if IsIsomorphicGraph(GRAin, GRAreturn)=false then
    Error("Bug in the reordering");
  fi;
  return GRAreturn;
end;


GRAPH_ZeroExtension:=function(GRA, nbZero)
  local nbPt, GRAret, i, eAdj;
  nbPt:=GRA.order;
  GRAret:=NullGraph(Group(()), nbPt + nbZero);
  for i in [1..nbPt]
  do
    for eAdj in Adjacency(GRA, i)
    do
      AddEdgeOrbit(GRAret, [i, eAdj]);
    od;
  od;
  return GRAret;
end;



CombinatorialModelGraphSubset:=function(TheGRA, TheSub)
  local NBV, NewGRA, iVert, jVert, eVert, ThePartition;
  NBV:=TheGRA.order;
  NewGRA:=NullGraph(Group(()), NBV+1);
  for iVert in [1..NBV-1]
  do
    for jVert in [iVert+1..NBV]
    do
      if IsEdge(TheGRA, [iVert, jVert]) then
        AddEdgeOrbit(NewGRA, [iVert, jVert]);
        AddEdgeOrbit(NewGRA, [jVert, iVert]);
      fi;
    od;
  od;
  for eVert in TheSub
  do
    AddEdgeOrbit(NewGRA, [eVert, NBV+1]);
    AddEdgeOrbit(NewGRA, [NBV+1, eVert]);
  od;
  ThePartition:=[[1..NBV], [NBV+1]];
  return rec(GRA:=NewGRA, ThePartition:=ThePartition);
end;


CharacteristicGraphOfSubset:=function(TheGRA, TheSub)
  local TheModel, CanonDesc;
  TheModel:=CombinatorialModelGraphSubset(TheGRA, TheSub);
  CanonDesc:=CanonicalRepresentativeVertexColoredGraph(TheModel.GRA, TheModel.ThePartition).CanonicalDesc;
  return __GetGraph6Expression(CanonDesc);
end;


GRAPH_Pyramid:=function(GRA)
  local nbVert, GRAvert, iVert, eAdj;
  nbVert:=GRA.order;
  GRAvert:=NullGraph(Group(()), nbVert+1);
  for iVert in [1..nbVert]
  do
    for eAdj in Adjacency(GRA, iVert)
    do
      AddEdgeOrbit(GRAvert, [iVert, eAdj]);
      AddEdgeOrbit(GRAvert, [eAdj, iVert]);
    od;
  od;
  for iVert in [1..nbVert]
  do
    AddEdgeOrbit(GRAvert, [iVert, nbVert+1]);
    AddEdgeOrbit(GRAvert, [nbVert+1, iVert]);
  od;
  return GRAvert;
end;

GRAPH_Cycle:=function(n)
  local GRA, iVert, iNext;
  GRA:=NullGraph(Group(()), n);
  for iVert in [1..n]
  do
    if iVert=n then
      iNext:=1;
    else
      iNext:=iVert+1;
    fi;
    AddEdgeOrbit(GRA, [iVert, iNext]);
    AddEdgeOrbit(GRA, [iNext, iVert]);
  od;
  return GRA;
end;

GRAPH_Path:=function(n)
  local GRA, iVert, iNext;
  GRA:=NullGraph(Group(()), n);
  for iVert in [1..n-1]
  do
    iNext:=iVert+1;
    AddEdgeOrbit(GRA, [iVert, iNext]);
    AddEdgeOrbit(GRA, [iNext, iVert]);
  od;
  return GRA;
end;


# Here we follow Nicolas D. RoussoPoulos
# "A max(m,n) algorithm for determining the graph H from its line graph G"
# Information processing letters 2(1973) 108-112
StartingCell:=function(G)
  local TT, A, eC, Adj, Elt, h, k, r, s, i, j, SE, oddness, Lodd, test; 
  A:=Adjacency(G, 1);
  eC:=A[1];
  Adj:=Intersection(Adjacency(G, eC), A);
  r:=Length(Adj);
  if r=0 then
    return [1, eC];
  else
    if r=1 then
      Elt:=Adj[1];
      h:=Length(Intersection(Adjacency(G, Elt), Adjacency(G, 1)));
      k:=Length(Intersection(Adjacency(G, Elt), Adjacency(G, eC)));
      if h=1 and k=1 then
        return [1, eC, Elt];
      else
        if h>1 then
          TT:=[Elt, 1];
        else
          TT:=[Elt, eC];
        fi;
      fi;
    else
      TT:=[1, eC];
    fi;
  fi;
  Adj:=Intersection(Adjacency(G, TT[1]), Adjacency(G, TT[2]));
  r:=Length(Adj);
  Lodd:=[];
  for i in Adj
  do
    SE:=Difference([1..G.order], Set([i, TT[1], TT[2]]));
    test:=1;
    for j in SE
    do
      oddness:=Length(Intersection(Adjacency(G, j), [i, TT[1], TT[2]]));
      if oddness=1 or oddness=3 then
        test:=0;
      fi;
    od;
    # if test=0 then the triangle is odd
    if test=0 then
      Lodd:=Union(Lodd, [i]);
    fi;
  od;
  s:=Size(Lodd);
  if r=2 and s=0 then
    return [Adj[1], TT[1], TT[2]];
  else
    if (s = r) or (s = r-1) then
      # test if clique
      Lodd:=Union(Lodd, Set(TT));
      for i in [1..Length(Lodd)-1]
      do
        for j in [i+1..Length(Lodd)]
        do
          if IsEdge(G, [Lodd[i], Lodd[j]])=false then 
            return false;
          fi;
        od;
      od;
      return Lodd;
    else
      return false;
    fi;
  fi;
end;



InverseLineGraphConnected:=function(G)
  local nbVert, TotalEdge, Tot, P, C, Adj, i, j, Cs, loop, Adding, nb, Gens, GenNew, L, iGen, iP, Ps, GroupH, O, iO, Q, Sete, H, Edge, Label, iElt, eS;
  nbVert:=G.order;
  TotalEdge:=[];
  for i in [1..nbVert]
  do
    TotalEdge[i]:=Adjacency(G, i);
  od;
  Print("INITIAL:\n");
  for i in [1..nbVert]
  do
    Print("    i=", i, " |adj|=", Length(TotalEdge[i]), " adj=", TotalEdge[i], "\n");
  od;
  C:=StartingCell(G);
  Print("C=", C, "\n");
  if C=false then
    return false;
  fi;
  P:=[C];
  for i in C
  do
    TotalEdge[i]:=Difference(TotalEdge[i], Set(C));
  od;
  Tot:=0;
  for i in [1..G.order]
  do
    Tot:=Tot+Length(TotalEdge[i]);
  od;
  Tot:=Tot/2;
  Print("CONTROL: Tot=", Tot, "\n");
  for i in [1..nbVert]
  do
    Print("    i=", i, " |adj|=", Length(TotalEdge[i]), " adj=", TotalEdge[i], "\n");
  od;
  Cs:=Set(C);
  # running the iteration loop to get the P set
  while (Tot>0)
  do
    Print("Tot=", Tot, "\n");
    for i in Cs
    do
      if Length(TotalEdge[i])>0 then
        Adding:=i;
        break;
      fi;
    od;
    Print("Adding=", Adding, "\n");
    C:=Union(TotalEdge[Adding], [Adding]);
    Print("C=", C, "\n");
    for i in [1..Length(C)-1]
    do
      for j in [i+1..Length(C)]
      do
        if Position(TotalEdge[C[i]], C[j])=fail then
          return false;
        fi;
#        if IsEdge(G, [C[i], C[j]])=false then
#          return false;
#        fi;
      od;
    od;
    Add(P, C);
    Cs:=Union(Cs, C);
    for i in C
    do
      TotalEdge[i]:=Difference(TotalEdge[i],C);
    od;
    Print("Before |C|=", Length(C), " Tot=", Tot, "\n");
    Tot:=Tot-Length(C)*(Length(C)-1)/2;
    Print("CONTROL: Tot=", Tot, "\n");
    for i in [1..nbVert]
    do
      Print("    i=", i, " |adj|=", Length(TotalEdge[i]), " adj=", TotalEdge[i], "\n");
    od;
  od;
  #    Now determining the W set and add it to the P set (so P is now P\cup W)
  for i in [1..G.order]
  do
    nb:=0;
    for eS in P
    do
      if i in eS then
        nb:=nb+1;
      fi;
    od;
    if nb=1 then
      Add(P, [i]);
      Print("Inserting ", [i], "\n");
    fi;
  od;
  # NEED TO ADD the cases of H1, H2 and H3.
  # these three graphs H_1=L(K_{1,3}+x)
  #                    H_2=L(H_1)
  #                    H_3=L(K_4)
  # share the property that they have two different cell decompositions
  # and that the automorphism group of their inverse line graph have half 
  # size.
  # Find symetry group of the inverse line graph
  Gens:=GeneratorsOfGroup(G.group);
  GenNew:=[];
  for iGen in [1..Length(Gens)]
  do
    L:=[];
    for iP in [1..Length(P)]
    do
      Ps:=OnSets(P[iP],Gens[iGen]);
      L[iP]:=Position(P,Ps);
    od;
    GenNew[iGen]:=PermList(L);
  od;
  if GenNew=[] then
    GroupH:=Group(());
  else
    GroupH:=Group(GenNew);
  fi;
  H:=NullGraph(GroupH,Length(P));
  O:=Orbits(GroupH, Combinations([1..Length(P)],2),OnSets);
  for iO in [1..Length(O)]
  do
    Edge:=O[iO][1];
    if Intersection(P[Edge[1]],P[Edge[2]])<>[] then
      AddEdgeOrbit(H,Edge);
      AddEdgeOrbit(H,Reversed(Edge));
    fi;
  od;
  #   add names to vertex
#    Q:=[];
#    for i in [1..Length(P)]
#    do
#      Sete:=[];
#      for j in [1..Length(P[i])]
#      do
#	    Sete[j]:=G.names[P[i][j]];
#      od;
#      Q[i]:=Sete;
#    od;
#    AssignVertexNames(H,Q);
  # computing the set of edges it is easier to use in applications
  Label:=[];
  for iElt in [1..G.order]
  do
    Label[iElt]:=[];
    for iP in [1..Length(P)]
    do
      if iElt in P[iP] then
        Add(Label[iElt], iP);
      fi;
    od;
  od;
  return [H, Label];
end;





InverseLineGraph:=function(G)
  local C, iCon, U, idx, ListInd, ListU, nbV, Lbl, Lbl2, GraphH, iVert, u, ListLabel, iLabel, TheInv;
  C:=ConnectedComponents(G);
  idx:=0;
  ListU:=[];
  ListInd:=[];
  nbV:=0;
  for iCon in [1..Length(C)]
  do
    if Length(C[iCon])=1 then
      ListInd[iCon]:=CompleteGraph(Group(()),1);
      AssignVertexNames(ListInd[iCon],C[iCon]);
      TheInv:=[CompleteGraph(Group(()),2), [[1,2]]];
    else
      ListInd[iCon]:=InducedSubgraph(G, C[iCon]);
      TheInv:=InverseLineGraphConnected(ListInd[iCon]);
      if TheInv=false then
        return false;
      fi;
    fi;
    ListU[iCon]:=TheInv;
    nbV:=nbV + TheInv[1].order;
  od;
  GraphH:=NullGraph(Group(()),nbV);
  ListLabel:=[];
  idx:=0;
  for iCon in [1..Length(C)]
  do
    for iVert in [1..ListU[iCon][1].order]
    do
      for u in Adjacency(ListU[iCon][1],iVert)
      do
        AddEdgeOrbit(GraphH, [idx+iVert, idx+u]);
      od;
    od;
    for iLabel in [1..Length(ListInd[iCon].names)]
    do
      Lbl:=ListU[iCon][2][iLabel];
      Lbl2:=ListInd[iCon].names[iLabel];
      ListLabel[Lbl2]:=[idx+Lbl[1], idx+Lbl[2]];
    od;
    idx:=idx+ListU[iCon][1].order;
  od;
  return [GraphH, ListLabel];
end;

# a distance-preserving spanning tree T of G
SpanningTreeGraph:=function(G,v)
  local i, j, a, u, L, ET;
  L := Layers(G,v);
  ET:=[];
  for i in [2..Length(L)]
  do
    for u in L[i]
    do
      a:=Intersection(Adjacency(G,u),L[i-1])[1];
      AddSet(ET, Set([a,u]));
    od;
  od;
  return ET;
end;


InducedSubgraphFullSymmetry:=function(GRA, eSubset)
  local eGRAind, PermGRP, nbPoint, eGRAret, Opt, eOpt, ePt, eStab, OcandAdj, eOcand, eRepr;
  eGRAind:=InducedSubgraph(GRA, eSubset);
  PermGRP:=AutGroupGraph(eGRAind);
  nbPoint:=Length(eSubset);
  eGRAret:=NullGraph(PermGRP, nbPoint);
  Opt:=Orbits(PermGRP, [1..nbPoint], OnPoints);
  for eOpt in Opt
  do
    ePt:=eOpt[1];
    eStab:=Stabilizer(PermGRP, ePt, OnPoints);
    OcandAdj:=Orbits(eStab, [1..nbPoint], OnPoints);
    for eOcand in OcandAdj
    do
      eRepr:=eOcand[1];
      if IsEdge(eGRAind, [ePt, eRepr]) then
        AddEdgeOrbit(eGRAret, [ePt, eRepr]);
        AddEdgeOrbit(eGRAret, [eRepr, ePt]);
      fi;
    od;
  od;
  return eGRAret;
end;




# FuncSelect is a function of selection of graphs, it must be defined
# for all sizes of subgraphs.
# AskedSize is the size of the asked subgraphs.
FindOrbitSubGraphs:=function(nbv, Group, FuncSelect, AskedSize)
  local O, Cand, eOrb, iP, CandSec, Stab, O2, eO2, eCand, Repr;
  #
  O:=Orbits(Group, [1..nbv], OnPoints);
  Cand:=[];
  for eOrb in O
  do
    AddSet(Cand, [Minimum(eOrb)]);
  od;
  #
  for iP in [2..AskedSize]
  do
    CandSec:=[];
    for eCand in Cand
    do
      Stab:=Stabilizer(Group, eCand, OnSets);
      O2:=Orbits(Stab, Difference([1..nbv], eCand), OnPoints);
      for eO2 in O2
      do
        AddSet(CandSec, Union(eCand, [eO2[1]]));
      od;
    od;
    Cand:=[];
    for eCand in CandSec
    do
      if FuncSelect(eCand)=true then
        AddSet(Cand, eCand);
      fi;
    od;
    CandSec:=[];
    for eCand in Cand
    do
      Repr:=Minimum(Orbit(Group, eCand, OnSets));
      AddSet(CandSec, Repr);
    od;
    Cand:=CandSec;
#    Print("Find ",Length(Cand)," orbits at step ", iP, "\n");
  od;
  return Cand;
end;





IsKconnectedOrbitwise:=function(GGraph, K)
  local SymGrp, FuncSelect, eCand, IndGra;
  SymGrp:=AutGroupGraph(GGraph);
  FuncSelect:=function(V)
    return true;
  end;
  for eCand in FindOrbitSubGraphs(GGraph.order, SymGrp, FuncSelect, K-1)
  do
    IndGra:=InducedSubgraph(GGraph, Difference([1..GGraph.order], eCand));
    if IsConnectedGraph(IndGra)=false then
      return false;
    fi;
  od;
  return true;
end;

IsKconnected:=function(GGraph, K)
  local eCand, IndGra;
  for eCand in Combinations([1..GGraph.order], K-1)
  do
    IndGra:=InducedSubgraph(GGraph, Difference([1..GGraph.order], eCand));
    if IsConnectedGraph(IndGra)=false then
      return false;
    fi;
  od;
  return true;
end;


ExportGraphToPolyhedralCpp:=function(FileSave, GRA)
  local nbV, output, iVert, LAdj, eDeg, eVert;
  RemoveFileIfExist(FileSave);
  output:=OutputTextFile(FileSave, true);
  nbV:=GRA.order;
  AppendTo(output, nbV, "\n");
  for iVert in [1..nbV]
  do
    LAdj:=Adjacency(GRA, iVert);
    eDeg:=Length(LAdj);
    AppendTo(output, " ", eDeg, "\n");
    for eVert in LAdj
    do
      AppendTo(output, " ", eVert-1);
    od;
    AppendTo(output, "\n");
  od;
  CloseStream(output);
end;


PrintGraphCppPolyhedral:=function(eFile, GRA)
  local output, nbV, LAdj, eVal, iV;
  output:=OutputTextFile(eFile, true);
  nbV:=GRA.order;
  AppendTo(output, nbV, "\n");
  for iV in [1..nbV]
  do
    LAdj:=Adjacency(GRA, iV);
    AppendTo(output, Length(LAdj), "\n");
    for eVal in LAdj
    do
      AppendTo(output, " ", eVal-1);
    od;
    AppendTo(output, "\n");
  od;
  CloseStream(output);
end;



MyCayleyGraph:=function(GRP, ListGen)
  local ListSeq, eElt, nbSeq, GRA, iSeq, eGen, fElt, pos;
  ListSeq:=[];
  for eElt in GRP
  do
    Add(ListSeq, eElt);
  od;
  nbSeq:=Length(ListSeq);
  GRA:=NullGraph(Group(()), nbSeq);
  for iSeq in [1..nbSeq]
  do
    eElt:=ListSeq[iSeq];
    for eGen in ListGen
    do
      fElt:=eElt*eGen;
      pos:=Position(ListSeq, fElt);
      AddEdgeOrbit(GRA, [iSeq, pos]);
      AddEdgeOrbit(GRA, [pos, iSeq]);
    od;
  od;
  if IsSimpleGraph(GRA)=false then
    Error("GRA must be a simple graph");
  fi;
  return rec(ListSeq:=ListSeq, GRA:=GRA);
end;




GetEmbeddingDistanceMatrix:=function(eEmbed)
  local nbVert, DistMat, iVert, jVert, eDiff, eNorm, n;
  nbVert:=Length(eEmbed);
  n:=Length(eEmbed[1]);
  DistMat:=NullMat(nbVert, nbVert);
  for iVert in [1..nbVert]
  do
    for jVert in [1..nbVert]
    do
      eDiff:=eEmbed[iVert] - eEmbed[jVert];
      eNorm:=Length(Filtered([1..n], x->AbsInt(eDiff[x])=1));
      DistMat[iVert][jVert]:=eNorm;
    od;
  od;
  return DistMat;
end;



LineGraph:=function(GRA)
  local nbVert, ListEdge, iVert, eAdj, nbEdge, GRAret, iEdge, jEdge, eInt;
  nbVert:=GRA.order;
  ListEdge:=[];
  for iVert in [1..nbVert]
  do
    for eAdj in Adjacency(GRA, iVert)
    do
      if eAdj > iVert then
        Add(ListEdge, [iVert, eAdj]);
      fi;
    od;
  od;
  nbEdge:=Length(ListEdge);
  GRAret:=NullGraph(Group(()), nbEdge);
  for iEdge in [1..nbEdge-1]
  do
    for jEdge in [iEdge+1..nbEdge]
    do
      eInt:=Intersection(ListEdge[iEdge], ListEdge[jEdge]);
      if Length(eInt)=1 then
        AddEdgeOrbit(GRAret, [iEdge, jEdge]);
        AddEdgeOrbit(GRAret, [jEdge, iEdge]);
      fi;
    od;
  od;
  return GRAret;
end;

ListListAdj_to_GRA:=function(ListListAdj)
  local nbVert, GRA, iVert, eAdj;
  nbVert:=Length(ListListAdj);
  GRA:=NullGraph(Group(()), nbVert);
  for iVert in [1..nbVert]
  do
    for eAdj in ListListAdj[iVert]
    do
      AddEdgeOrbit(GRA, [iVert, eAdj]);
      AddEdgeOrbit(GRA, [eAdj, iVert]);
    od;
  od;
  return GRA;
end;


DecideLineGraphnessExhaustive:=function(GRA,nbVertSearch)
  local ListGRA, eGRA, GRAline, eLLA;
  ListGRA:=GetIsomorphismTypeGraph(nbVertSearch);
  for eLLA in ListGRA
  do
    eGRA:=ListListAdj_to_GRA(eLLA);
    GRAline:=LineGraph(eGRA);
    if IsIsomorphicGraph(GRAline, GRA)=true then
      return rec(success:=true, GRA:=eGRA);
    fi;
  od;
  return rec(success:=false);
end;


SymmetrizedVersionOfGraph:=function(GR)
  local nbVert, GRA, i, j;
  nbVert:=GR.order;
  GRA:=NullGraph(Group(()), nbVert);
  for i in [1..nbVert]
  do
    for j in [1..nbVert]
    do
      if i<>j then
        if IsEdge(GR, [i,j]) then
          AddEdgeOrbit(GRA, [i,j]);
          AddEdgeOrbit(GRA, [j,i]);
        fi;
      fi;
    od;
  od;
  return GRA;
end;

IsGroupAutomorphism:=function(GRA, GRP)
  local nbVert, IsAutom, eGen;
  nbVert:=GRA.order;
  IsAutom:=function(eElt)
    local i, j, iImg, jImg;
    for i in [1..nbVert]
    do
      for j in [1..nbVert]
      do
        iImg:=OnPoints(i, eElt);
        jImg:=OnPoints(j, eElt);
        if IsEdge(GRA, [i,j])<>IsEdge(GRA, [iImg, jImg]) then
          return false;
        fi;
      od;
    od;
    return true;
  end;
  for eGen in GeneratorsOfGroup(GRP)
  do
    if IsAutom(eGen)=false then
      return false;
    fi;
  od;
  return true;
end;

GetSymmetricGraphFromListEdge:=function(n, ListEdge)
  local eGR, eEdge, i, j;
  eGR:=NullGraph(Group(()), n);
  for eEdge in ListEdge
  do
    i:=eEdge[1];
    j:=eEdge[2];
    AddEdgeOrbit(eGR, [i,j]);
    AddEdgeOrbit(eGR, [j,i]);
  od;
  return eGR;
end;

GetProofNonSimplicity:=function(GRA)
  local nbVert, iVert, jVert;
  nbVert:=GRA.order;
  for iVert in [1..nbVert]
  do
    for jVert in Adjacency(GRA, iVert)
    do
      if Position(Adjacency(GRA, jVert), iVert)=fail then
        return [iVert, jVert];
      fi;
    od;
  od;
  return "seems to be simple after all";
end;
