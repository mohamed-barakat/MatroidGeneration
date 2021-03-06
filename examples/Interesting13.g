LoadPackage( "MatroidGeneration" );
db := AttachMatroidsDatabase();
d := db.matroids_split_public.document("118cb9babc77e406eb53043ac399bf851a012830");
matroid := MatroidByCoatomsNC( d );
#homalgIOMode( "f" );
ZZ := HomalgRingOfIntegersInSingular( );
SetInfoLevel( InfoWarning, 0 );
M := EquationsAndInequationsOfModuliSpaceOfMatroid( matroid, ZZ );
LoadPackage( "ZariskiFrames" );
m := DistinguishedQuasiAffineSet( M );
e := EmbedInSmallerAmbientSpace( m );
a := DistinguishedLocallyClosedPart( e );
