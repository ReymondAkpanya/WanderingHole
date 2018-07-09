


#!	@Description
#!	Find the canonical form of a surface, with its lex least numbering of faces, edges and vertices,
#! 	and also provide the maps between the elements of the original surface and the canonical surface.

#! The following example illustrates the use of the CanonicalRepresentativeOfPolygonalSurface
#! command. We define the cube, but with a labelling of larger than necessary integers.  
#! CanonicalRepresentativeOfPolygonalSurface is then used to return both the canonical 
#! representative of the cube and the maps between the cube and its canon. The faces, edges 
#! and vertices are displayed and are clearly now lex least in their ordering, and some 
#! checks reveal that the cube is not identical to its canon, it is however isomorphic, and 
#! mapping the canon under its preimage map returns the cube again.

#! @ExampleSession
#! gap> faces := [ 20, 21, 22, 23, 24, 25 ];;
#! gap> edges := [ 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15 ];;
#! gap> vertices := [ 12, 13, 14, 15, 16, 17, 18, 19 ];;
#! gap> edgesoffaces := [ ,,,,,,,,,,,,,,,,,,, [ 4, 5, 6, 7 ], [ 4, 8, 11, 15 ], 
#! [ 5, 8, 9, 12 ], [ 7, 10, 11, 14 ], [ 6, 9, 10, 13 ], [ 12, 13, 14, 15 ] ];;
#! gap> verticesofedges := [ ,,, [ 12, 13 ], [ 13, 14 ], [ 14, 15 ], [ 12, 15 ], [ 13, 17 ], [ 14, 18 ], [ 15, 19 ], [ 12, 16 ], [ 17, 18 ], [ 18, 19 ], [ 16, 19 ], [ 16, 17 ] ];;
#! gap> cube := PolygonalSurfaceByDownwardIncidence(vertices, edges, faces, verticesofedges, edgesoffaces);;
#! gap> canonicalcube:=CanonicalRepresentativeOfPolygonalSurface(cube);;
#! gap> canon:=canonicalcube[1];;
#! gap> preimage:=MappingOfSurfaces(canon, canonicalcube[2][1], canonicalcube[2][2], canonicalcube[2][3]);;
#! gap> Faces(canon);
#! [ 1, 2, 3, 4, 5, 6 ]
#! gap> Edges(canon);
#! [ 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12 ]
#! gap> Vertices(canon);
#! [ 1, 2, 3, 4, 5, 6, 7, 8 ]
#! gap> EdgesOfFaces(canon);
#! [ [ 1, 2, 3, 4 ], [ 5, 6, 7, 8 ], [ 1, 5, 9, 10 ], [ 3, 7, 9, 11 ], [ 4, 8, 10, 12 ], [ 2, 6, 11, 12 ] ]
#! gap> VerticesOfEdges(canon);
#! [ [ 1, 2 ], [ 3, 4 ], [ 1, 3 ], [ 2, 4 ], [ 5, 6 ], [ 7, 8 ], [ 5, 7 ], [ 6, 8 ], [ 1, 5 ], [ 2, 6 ], [ 3, 7 ], [ 4, 8 ] ]
#! gap> canon=cube;
#! false
#! gap> IsIsomorphicPolygonalComplex(cube, canon);
#! true
#! gap> preimage=cube;
#! true
#! @EndExampleSession

#!	@Arguments A polygonal surface
#!	@Returns A list containing the canonical form of the surface and maps from the new
#!	face, edge and point set respectively, to the old face, edge and point set.
# DeclareOperation( "CanonicalRepresentativeOfPolygonalSurface", [IsPolygonalSurface]);


# InstallMethod( CanonicalRepresentativeOfPolygonalSurface, 
# 	"for a polygonal surface", [IsPolygonalSurface],
CanonicalRepresentativeOfPolygonalSurface2 := 
	function( surf )
		local originalfacesofsurf, originaledgesofsurf, originalverticesofsurf,
		totalgraphverts, mapfaces, mapedges, mapvertices, currentvert, i, vertsofgraph,
		edges, edgesofface, j, verticesofface, verticesofedge, graph, perm, perminv, 
		edgesoffacesofsurf, F, edgesofface2, verticesofedgesofsurf, e, verticesofedge2,
		newfaces, newedges, newvertices, n1, n2, n3,
		mapfaces2, mapedges2, mapvertices2, edgesoffacesofsurf2, verticesofedgesofsurf2,
		surf2, surf3, colours, inversefacemap, inverseedgemap, inversevertexmap;


		# The original faces/edges/vertices of surf
		originalfacesofsurf := Faces(surf); 
		originaledgesofsurf := Edges(surf);
		originalverticesofsurf := Vertices(surf);
		# The number of faces/edges/vertices of surf
		n1 := NumberOfFaces(surf);
		n2 := NumberOfEdges(surf);
		n3 := NumberOfVertices(surf);
		# Total number of elements of surf - we make a bijection with the elements
		totalgraphverts := n1+n2+n3;

		# Create maps from the elements to the new labels.
		# Map faces to [1 .. n1], edges to [n1+1 .. n1+n2] and vertices to [n1+n2+1 .. totalverts]
		# Let i be a face, then the i maps to mapfaces[i]
		mapfaces := ListWithIdenticalEntries(Maximum(originalfacesofsurf), 0);
		mapedges := ListWithIdenticalEntries(Maximum(originaledgesofsurf), 0);
		mapvertices := ListWithIdenticalEntries(Maximum(originalverticesofsurf), 0);
		# Also assign each element a colour - faces are 1, edges are 2, vertices are 3
		# Let i be an element of surf with the new labelling. Then the colour can be
		# established with colours[i]
		colours:=[];
		currentvert:=0;
		for i in originalfacesofsurf do
			currentvert := currentvert + 1;
			mapfaces[i] := currentvert;
			Add(colours, 1);
		od;
		for i in originaledgesofsurf do
			currentvert := currentvert + 1;
			mapedges[i] := currentvert;
			Add(colours, 2);
		od;
		for i in originalverticesofsurf do
			currentvert := currentvert + 1;
			mapvertices[i] := currentvert;
			Add(colours, 3);
		od;


		# Create the corresponding graph.
		# The elements of surf form the vertices of the graph.
		# There is an edge in the graph if the corresponding elements of surf are incident.
		vertsofgraph := [1 .. totalgraphverts];

		# Loop through the faces and for each face loop through vertices and edges.
		# If the face is incident with the edge/vertex, put an edge in the graph.
		edges := [];
		for i in originalfacesofsurf do
			edgesofface := EdgesOfFace( surf, i);
			for j in edgesofface do
				Add(edges, [mapfaces[i], mapedges[j]]);
			od; 
			verticesofface := VerticesOfFace( surf, i);
			for j in verticesofface do
				Add(edges, [mapfaces[i], mapvertices[j]]);
			od; 
		od;
		# Repeat for edges. Only need to check for vertices, since we did faces-edges above.
		for i in originaledgesofsurf do
			verticesofedge := VerticesOfEdge( surf, i);
			for j in verticesofedge do
				Add(edges, [mapedges[i], mapvertices[j]]);
			od; 
		od;
		# No need to loop through vertices, since vertices are not incident with vertices,
		# and incidence with faces/edges done above.

		# Find the canonical form of the graph with Nauty,
		# preserving the colours (ie  map faces to faces, edges to edge etc...)
		graph := NautyColoredGraph(edges, colours);
		# Find the permutation which will map the old vertices to the new.
		perminv := CanonicalLabeling(graph);
		perm := perminv^(-1);

		# Now that we have the canonical labelling, we can write the surface in canonical form.
		# First take a face and write it by its edges
		# Map the face to its new labelling, and then permute to canonical form.
		# Map the edges to the new labelling
		# Permute the newly labelled eges to their canonical form.
		# Now put the edges in the list of FacesByEdges
		edgesoffacesofsurf := [];
		for i in originalfacesofsurf do
			F := mapfaces[i]^perm;
			edgesofface := EdgesOfFace( surf, i);
			edgesofface2 := List(edgesofface, t -> mapedges[t]^perm);
			edgesoffacesofsurf[F] := edgesofface2;;
		od;

		# Same as above, but for edges with respect to vertices
		verticesofedgesofsurf := [];
		for i in originaledgesofsurf do
			e := mapedges[i]^perm;
			verticesofedge := VerticesOfEdge( surf, i);
			verticesofedge2 := List(verticesofedge, t -> mapvertices[t]^perm);
			verticesofedgesofsurf[e] := verticesofedge2;;
		od;


		# Map the elements to the new labelling, then permute to canonical form
		newfaces := Set(originalfacesofsurf, t -> mapfaces[t]^perm);
		newedges := Set(originaledgesofsurf, t -> mapedges[t]^perm);
		newvertices := Set(originalverticesofsurf, t -> mapvertices[t]^perm);

		# Now that we have the newly labelled, canonical elements,
		# we map them a lex least labelling.
		# We simply take the set of the new + canonical labels and make a bijection to
		# its position in the set.
		mapfaces2 := [];
		for i in [1 .. Size(newfaces)] do
			mapfaces2[newfaces[i]] := i;
		od;
		mapedges2 := [];
		for i in [1 .. Size(newedges)] do
			mapedges2[newedges[i]] := i;
		od;
		mapvertices2 := [];
		for i in [1 .. Size(newvertices)] do
			mapvertices2[newvertices[i]] := i;
		od;

		edgesoffacesofsurf2 := [];
		for i in newfaces do
			F := mapfaces2[i];
			edgesoffacesofsurf2[F] := List(edgesoffacesofsurf[i], t -> mapedges2[t]);;
		od;

		verticesofedgesofsurf2 := [];
		for i in newedges do
			e := mapedges2[i];
			verticesofedgesofsurf2[e] := List(verticesofedgesofsurf[i], t -> mapvertices2[t]);;
		od;

		# To get the inverse map, we reverse the lex least map,
		# then the canonical permuting, then the bijection to new labelling.
		inversefacemap:= List([1 .. n1], t -> Position(mapfaces2, t));
		inversefacemap:= List(inversefacemap, t -> t^perminv);
		inversefacemap:= List(inversefacemap, t -> Position(mapfaces, t));
		inverseedgemap:= List([1 .. n2], t -> Position(mapedges2, t));
		inverseedgemap:= List(inverseedgemap, t -> t^perminv);
		inverseedgemap:= List(inverseedgemap, t -> Position(mapedges, t));
		inversevertexmap:= List([1 .. n3], t -> Position(mapvertices2, t));
		inversevertexmap:= List(inversevertexmap, t -> t^perminv);
		inversevertexmap:= List(inversevertexmap, t -> Position(mapvertices, t));

		surf2 := PolygonalSurfaceByDownwardIncidence(verticesofedgesofsurf2, edgesoffacesofsurf2);

		# return the canonical form of the surface and
		# the bijcetions mapping the new elements to old, by element i in canonical surface
		# maps to inversemap[i] in the old surface.
		return [surf2, [inversefacemap, inverseedgemap, inversevertexmap]];
	end
;


#!	@Description
#!	Takes a surface and maps between from the faces, edges and vertices, and returns the surface
#!	under the mapping. The maps are given as lists, with the position of the list indexed by
#!	the input of the map (that is, the face/edge/vertex of the given surface) and the value at
#!	that position is the image under the map.
#!	@Arguments A polygonal surface, facemap, edgemap, vertexmap
#!	@Returns a simplicial surface
DeclareOperation( "MappingOfSurfaces", [IsPolygonalSurface, IsList, IsList, IsList]);




InstallMethod( MappingOfSurfaces, 
	"for a surface and three lists", [IsPolygonalSurface, IsList, IsList, IsList],
	function(surf, mapfaces, mapedges, mapvertices)
		local edgesoffaces, face, f2, edgesofface, newedgesofface, verticesofedge, verticesofedges,
		e2, newverticesofedge, newfaces, newedges, newvertices, edge;
		edgesoffaces:=[];
		for face in Faces(surf) do
			f2 := mapfaces[face];
			edgesofface:=EdgesOfFace(surf, face);
			newedgesofface := List(edgesofface, t -> mapedges[t]);
			edgesoffaces[f2]:= Set(newedgesofface);
		od;

		verticesofedges:=[];
		for edge in Edges(surf) do
			e2 := mapedges[edge];
			verticesofedge:=VerticesOfEdge(surf, edge);
			newverticesofedge := List(verticesofedge, t -> mapvertices[t]);
			verticesofedges[e2]:= Set(newverticesofedge);
		od;
		newfaces:=Set(Faces(surf), t -> mapfaces[t]);
		newedges := Set(Edges(surf), t -> mapedges[t]);
		newvertices:=Set(Vertices(surf), t -> mapvertices[t]);
		return PolygonalSurfaceByDownwardIncidence(newvertices, newedges, newfaces, verticesofedges, edgesoffaces);
	end
);
