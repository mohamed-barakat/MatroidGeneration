LoadPackage( "alcove", ">= 2023.09-02" );
LoadPackage( "LinearAlgebraForCAP" );
#LoadPackage( "FinSetsForCAP" );

zz := HomalgRingOfIntegers( );
QQ := HomalgFieldOfRationals( );

Zmat := CategoryOfRows( zz );
Qmat := MatrixCategory( QQ );

kmat := Qmat;

BooleanArrangement :=
  function( r )
    local id;
    
    id := HomalgIdentityMatrix( r, QQ );
    
    return Matroid( id );
    
end;

BraidArrangement :=
  function( r )
    local id, z, j, pair;
    
    id := HomalgIdentityMatrix( r, QQ );
    
    z := HomalgInitialMatrix( r, Binomial( r, 2 ), QQ );
    
    j := 1;
    
    for pair in IteratorOfCombinations( [ 1 .. r ], 2 ) do
        
        SetMatElm( z, pair[1], j, 1 );
        SetMatElm( z, pair[2], j, -1 );
        j := j + 1;
        
    od;
    
    return Matroid( UnionOfColumns( id, z ) );
    
end;

# WRONG:
#ImageOfBraidGroup :=
#  function( r )
#    
#    return Image( ActionHomomorphism( SymmetricGroup( r + 1 ), Combinations( [ 1 .. r + 1 ], 2 ), OnSets ) );
#    
#end;

DeclareOperation( "OrlikSolomonFlatsOfCorankOneOfFlat",
        [ IsMatroid, IsList ] );

DeclareOperation( "OrlikSolomonFlatsOfCorankTwoOfFlat",
        [ IsMatroid, IsList ] );

DeclareOperation( "OrlikSolomonSpacesOfCorankOneOfFlat",
        [ IsMatroid, IsList ] );

DeclareOperation( "OrlikSolomonSpacesOfCorankTwoOfFlat",
        [ IsMatroid, IsList ] );

DeclareOperation( "OrlikSolomonCodifferentialBetweenAPairOfFlatsWithGivenObjects",
        [ IsMatroid, IsList, IsList, IsCapCategoryObject, IsCapCategoryObject ] );

DeclareOperation( "OrlikSolomonLastButOneCodifferentialOfLocalizationWithGivenObjects",
        [ IsMatroid, IsList, IsCapCategoryObject, IsCapCategoryObject ] );

DeclareOperation( "OrlikSolomonLastButOneCodifferentialOfLocalization",
        [ IsMatroid, IsList ] );

DeclareOperation( "OrlikSolomonEmbeddingOfSpaceOfFlatWithGivenRange",
        [ IsMatroid, IsList, IsCapCategoryObject ] );

DeclareOperation( "OrlikSolomonSpaceOfFlat",
        [ IsMatroid, IsList ] );

#! @Arguments source_matroid, target_matroid, flat, map, source, range
DeclareOperation( "OrlikSolomonMorphismBetweenDirectSumOfCorankOneSpacesOfFlatsWithGivenObjects",
        [ IsMatroid, IsMatroid, IsList, IsList, IsCapCategoryObject, IsCapCategoryObject ] );

#! @Arguments source_matroid, target_matroid, flat, map, source, range
DeclareOperation( "OrlikSolomonMorphismBetweenSpacesOfFlatsWithGivenObjects",
        [ IsMatroid, IsMatroid, IsList, IsList, IsCapCategoryObject, IsCapCategoryObject ] );

#! @Arguments source_matroid, target_matroid, flat, map
DeclareOperation( "OrlikSolomonMorphismBetweenSpacesOfFlats",
        [ IsMatroid, IsMatroid, IsList, IsList ] );

## { OS_S }_{S ≤₁ X}
InstallMethodWithCache( OrlikSolomonFlatsOfCorankOneOfFlat,
        [ IsMatroid, IsList ],
        
  function( matroid, X )
    local rkX, Ss, Ts;
    
    rkX := RankFunction( matroid )( X );
    
    if rkX < 1 then
        Error( "the given flat X is of rank < 1\n" );
    fi;
    
    return Filtered( FlatsOfRank( matroid, rkX - 1 ), S -> IsSubset( X, S ) );
    
end );

## { OS_T }_{T ≤₂ X}
InstallMethodWithCache( OrlikSolomonFlatsOfCorankTwoOfFlat,
        [ IsMatroid, IsList ],
        
  function( matroid, X )
    local rkX;
    
    rkX := RankFunction( matroid )( X );
    
    if rkX < 2 then
        Error( "the given flat X is of rank < 2\n" );
    fi;
    
    return Filtered( FlatsOfRank( matroid, rkX - 2 ), T -> IsSubset( X, T ) );
    
end );

## ⨁_{S ≤₁ X} OS_S
InstallMethodWithCache( OrlikSolomonSpacesOfCorankOneOfFlat,
        [ IsMatroid, IsList ],
        
  function( matroid, X )
    local rkX;
    
    rkX := RankFunction( matroid )( X );
    
    if rkX <= 0 then
        return [ ];
    fi;
    
    return List( OrlikSolomonFlatsOfCorankOneOfFlat( matroid, X ), S -> OrlikSolomonSpaceOfFlat( matroid, S ) );
    
end );

## ⨁_{T ≤₂ X} OS_T
InstallMethodWithCache( OrlikSolomonSpacesOfCorankTwoOfFlat,
        [ IsMatroid, IsList ],
        
  function( matroid, X )
    local rkX;
    
    rkX := RankFunction( matroid )( X );
    
    if rkX <= 1 then
        return [ ];
    fi;
    
    return List( OrlikSolomonFlatsOfCorankTwoOfFlat( matroid, X ), T -> OrlikSolomonSpaceOfFlat( matroid, T ) );
    
end );

## d_{X,S}: OS_S ← OS_X
InstallMethodWithCache( OrlikSolomonCodifferentialBetweenAPairOfFlatsWithGivenObjects,
        [ IsMatroid, IsList, IsList, IsCapCategoryObject, IsCapCategoryObject ],
        
  function( matroid, X, S, OS_X, OS_S )
    local Ss, k, OS_Ss;
    
    Ss := OrlikSolomonFlatsOfCorankOneOfFlat( matroid, X );
    
    k := Position( Ss, S );
    
    if k = fail then
        
        return ZeroMorphism( kmat,
                       OS_X,
                       OS_S );
        
    fi;
    
    OS_Ss := OrlikSolomonSpacesOfCorankOneOfFlat( matroid, X );
    
    return ComponentOfMorphismIntoDirectSum( kmat,
                   OrlikSolomonEmbeddingOfSpaceOfFlatWithGivenRange( matroid, X, DirectSum( kmat, OS_Ss ) ),
                   OS_Ss,
                   k );
    
end );

## ⨁_{T ≤₂ X} OS_T ← ⨁_{S ≤₁ X} OS_S
InstallMethodWithCache( OrlikSolomonLastButOneCodifferentialOfLocalizationWithGivenObjects,
        [ IsMatroid, IsList, IsCapCategoryObject, IsCapCategoryObject ],
        
  function( matroid, X, OS_S, OS_T )
    local rkX, Ss, Ts, OS_Ss, OS_Ts;
    
    rkX := RankFunction( matroid )( X );
    
    if rkX < 2 then
        Error( "the given flat X is of rank < 2\n" );
    fi;
    
    Ss := OrlikSolomonFlatsOfCorankOneOfFlat( matroid, X );
    Ts := OrlikSolomonFlatsOfCorankTwoOfFlat( matroid, X );
    
    OS_Ss := OrlikSolomonSpacesOfCorankOneOfFlat( matroid, X );
    OS_Ts := OrlikSolomonSpacesOfCorankTwoOfFlat( matroid, X );
    
    return MorphismBetweenDirectSumsWithGivenDirectSums( kmat,
                   OS_S,
                   OS_Ss,
                   List( [ 1 .. Length( Ss ) ], s ->
                         List( [ 1 .. Length( Ts ) ], t ->
                               OrlikSolomonCodifferentialBetweenAPairOfFlatsWithGivenObjects( matroid, Ss[s], Ts[t], OS_Ss[s], OS_Ts[t] ) ) ),
                   OS_Ts,
                   OS_T );
    
end );

## ⨁_{T ≤₂ X} OS_T ← ⨁_{S ≤₁ X} OS_S
InstallMethodWithCache( OrlikSolomonLastButOneCodifferentialOfLocalization,
        [ IsMatroid, IsList ],
        
  function( matroid, X )
    
    return OrlikSolomonLastButOneCodifferentialOfLocalizationWithGivenObjects( matroid, X,
                   DirectSum( kmat, OrlikSolomonSpacesOfCorankOneOfFlat( matroid, X ) ),
                   DirectSum( kmat, OrlikSolomonSpacesOfCorankTwoOfFlat( matroid, X ) ) );
    
end );

## ⨁_{S ≤₁ X} OS_S ↩ OS_X
InstallMethodWithCache( OrlikSolomonEmbeddingOfSpaceOfFlatWithGivenRange,
        [ IsMatroid, IsList, IsCapCategoryObject ],
        
  function( matroid, X, OS_S )
    local rkX, OS_T;
    
    rkX := RankFunction( matroid )( X );
    
    if rkX = 0 then
        return UniversalMorphismIntoZeroObject( kmat, TensorUnit( kmat ) );
    elif rkX = 1 then
        return IdentityMorphism( kmat, TensorUnit( kmat ) );
    fi;
    
    OS_T := DirectSum( kmat, OrlikSolomonSpacesOfCorankTwoOfFlat( matroid, X ) );
    
    return WeakKernelEmbedding( kmat,
                   OrlikSolomonLastButOneCodifferentialOfLocalizationWithGivenObjects( matroid, X, OS_S, OS_T ) );
    
end );

## OS_X
InstallMethodWithCache( OrlikSolomonSpaceOfFlat,
        [ IsMatroid, IsList ],
        
  function( matroid, X )
    
    return Source( OrlikSolomonEmbeddingOfSpaceOfFlatWithGivenRange( matroid, X, DirectSum( kmat, OrlikSolomonSpacesOfCorankOneOfFlat( matroid, X ) ) ) );
    
end );

## ⨁_{S' ≤₁ X} OS_S' → ⨁_{S ≤₁ f(X)} OS_S
InstallMethod( OrlikSolomonMorphismBetweenDirectSumOfCorankOneSpacesOfFlatsWithGivenObjects,
        [ IsMatroid, IsMatroid, IsList, IsList, IsCapCategoryObject, IsCapCategoryObject ],
        
  function( source_matroid, target_matroid, X, f, OS_source_S, OS_target_S )
    local rkX, fX, rkfX, source_Ss, target_Ss, OS_source_Ss, OS_target_Ss, g;
    
    rkX := RankFunction( source_matroid )( X );
    
    if rkX = 0 then
        return IdentityMorphism( kmat, TensorUnit( kmat ) );
    elif rkX = 1 then
        return IdentityMorphism( kmat, TensorUnit( kmat ) );
    fi;
    
    ## f(X)
    fX := Set( f{X} );
    
    rkfX := RankFunction( target_matroid )( fX );
    
    source_Ss := OrlikSolomonFlatsOfCorankOneOfFlat( source_matroid, X );
    target_Ss := OrlikSolomonFlatsOfCorankOneOfFlat( target_matroid, fX );
    
    OS_source_Ss := OrlikSolomonSpacesOfCorankOneOfFlat( source_matroid, X );
    OS_target_Ss := OrlikSolomonSpacesOfCorankOneOfFlat( target_matroid, fX );
    
    ##
    OS_target_S := DirectSum( kmat, OS_target_Ss );
    
    g :=
      function( S_ )
        local fS_, mor;
        
        ## f(S')
        fS_ := Set( f{S_} );
        
        ## OS_{S'} → OS_{f(S')}
        mor := OrlikSolomonMorphismBetweenSpacesOfFlatsWithGivenObjects( source_matroid, target_matroid, S_, f,
                       OrlikSolomonSpaceOfFlat( source_matroid, S_ ),
                       OrlikSolomonSpaceOfFlat( target_matroid, fS_ ) );
        
        ## f(S') = f(X)?
        if fS_ = fX then
            return PreCompose( kmat,
                           ## here: OS_{f(S')} = OS_{f(X)}
                           mor,
                           ## ⨁_{S ≤₁ f(X)} OS_S ↩ OS_{f(X)}
                           OrlikSolomonEmbeddingOfSpaceOfFlatWithGivenRange( target_matroid, fX, OS_target_S ) );
        fi;

        return PreCompose( kmat,
                       mor,
                       InjectionOfCofactorOfDirectSumWithGivenDirectSum( kmat,
                               OS_target_Ss,
                               SafePosition( target_Ss, fS_ ),
                               OS_target_S ) );
        
    end;
    
    return UniversalMorphismFromDirectSumWithGivenDirectSum( kmat,
                   OS_source_Ss,
                   OS_source_S,
                   List( source_Ss, g ),
                   OS_target_S );
    
end );

## OS(f): OS_X(L') → OS_f(X)(L)
InstallMethod( OrlikSolomonMorphismBetweenSpacesOfFlatsWithGivenObjects,
        [ IsMatroid, IsMatroid, IsList, IsList, IsCapCategoryObject, IsCapCategoryObject ],
        
  function( source_matroid, target_matroid, X, f, OS_X, OS_fX )
    local rkX, fX;
    
    rkX := RankFunction( source_matroid )( X );
    
    if rkX = 0 then
        return IdentityMorphism( kmat, TensorUnit( kmat ) );
    elif rkX = 1 then
        return IdentityMorphism( kmat, TensorUnit( kmat ) );
    fi;
    
    ## f(X)
    fX := Set( f{X} );
    
    return KernelObjectFunctorialWithGivenKernelObjects( kmat,
                   OS_X,
                   OrlikSolomonLastButOneCodifferentialOfLocalization( source_matroid, X ),
                   OrlikSolomonMorphismBetweenDirectSumOfCorankOneSpacesOfFlatsWithGivenObjects( source_matroid, target_matroid, X, f,
                           DirectSum( kmat, OrlikSolomonSpacesOfCorankOneOfFlat( source_matroid, X ) ),
                           DirectSum( kmat, OrlikSolomonSpacesOfCorankOneOfFlat( target_matroid, fX ) ) ),
                   OrlikSolomonLastButOneCodifferentialOfLocalization( target_matroid, fX ),
                   OS_fX );
    
end );

## OS(f): OS_X(L') → OS_f(X)(L)
InstallMethod( OrlikSolomonMorphismBetweenSpacesOfFlats,
        [ IsMatroid, IsMatroid, IsList, IsList ],
        
  function( source_matroid, target_matroid, X, f )
    local fX;
    
    ## f(X)
    fX := Set( f{X} );
    
    return OrlikSolomonMorphismBetweenSpacesOfFlatsWithGivenObjects( source_matroid, target_matroid, X, f,
                   OrlikSolomonSpaceOfFlat( source_matroid, X ),
                   OrlikSolomonSpaceOfFlat( target_matroid, fX ) );
    
end );


## Test:
r := 3;
L := BraidArrangement( r );
n := Length( GroundSet( L ) );
Assert( 0, n = Binomial( r + 1, 2 ) );
rkL := RankFunction( L );
muL := MoebiusFunction( L );
W := AutomorphismGroup( L );
Display( CharacterTable( W ) );

Assert( 0, ForAll( Concatenation( Flats( L ) ), X -> ObjectDatum( OrlikSolomonSpaceOfFlat( L, X ) ) = AbsInt( muL( X ) ) ) );
Assert( 0, ForAll( Concatenation( Flats( L ) ), X -> ObjectDatum( Source( OrlikSolomonMorphismBetweenSpacesOfFlats( L, L, X, GroundSet( L ) ) ) ) = AbsInt( muL( X ) ) ) );

OsL := SortedList( Orbits( W, Concatenation( Flats( L ) ), OnSets ), {a,b} -> Length(a[1]) < Length(b[1]) );
XsL := List( OsL, O -> O[1] );
GXsL := List( XsL, X -> Stabilizer( W, X, OnSets ) );
OSXsL := List( [ 1 .. Length( XsL ) ], k -> Group( List( GeneratorsOfGroup( GXsL[k] ), pi -> EntriesOfHomalgMatrixAsListList( UnderlyingMatrix( OrlikSolomonMorphismBetweenSpacesOfFlats( L, L, XsL[k], ListPerm( pi, n ) ) ) ) ) ) );
OSOsL := List( [ 1 .. Length( XsL ) ], k -> List( ConstituentsOfCharacter( InducedClassFunction( RestrictedClassFunction( NaturalCharacter( OSXsL[k] ), GroupHomomorphismByImages( GXsL[k], OSXsL[k] ) ), W ) ), ValuesOfClassFunction ) );
