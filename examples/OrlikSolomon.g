LoadPackage( "alcove", ">= 2023.09-02" );
LoadPackage( "LinearAlgebraForCAP" );
LoadPackage( "FinSetsForCAP" );

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

## { A_S }_{S ≤₁ X}
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

## { A_T }_{T ≤₂ X}
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

## ⨁_{S ≤₁ X} A_S
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

## ⨁_{T ≤₂ X} A_T
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

## d_{X,S}: A_S ← A_X
InstallMethodWithCache( OrlikSolomonCodifferentialBetweenAPairOfFlatsWithGivenObjects,
        [ IsMatroid, IsList, IsList, IsCapCategoryObject, IsCapCategoryObject ],
        
  function( matroid, X, S, A_X, A_S )
    local Ss, k, A_Ss;
    
    Ss := OrlikSolomonFlatsOfCorankOneOfFlat( matroid, X );
    
    k := Position( Ss, S );
    
    if k = fail then
        
        return ZeroMorphism( kmat,
                       A_X,
                       A_S );
        
    fi;
    
    A_Ss := OrlikSolomonSpacesOfCorankOneOfFlat( matroid, X );
    
    return ComponentOfMorphismIntoDirectSum( kmat,
                   OrlikSolomonEmbeddingOfSpaceOfFlatWithGivenRange( matroid, X, DirectSum( kmat, A_Ss ) ),
                   A_Ss,
                   k );
    
end );

## ⨁_{T ≤₂ X} A_T ← ⨁_{S ≤₁ X} A_S
InstallMethodWithCache( OrlikSolomonLastButOneCodifferentialOfLocalizationWithGivenObjects,
        [ IsMatroid, IsList, IsCapCategoryObject, IsCapCategoryObject ],
        
  function( matroid, X, A_S, A_T )
    local rkX, Ss, Ts, A_Ss, A_Ts;
    
    rkX := RankFunction( matroid )( X );
    
    if rkX < 2 then
        Error( "the given flat X is of rank < 2\n" );
    fi;
    
    Ss := OrlikSolomonFlatsOfCorankOneOfFlat( matroid, X );
    Ts := OrlikSolomonFlatsOfCorankTwoOfFlat( matroid, X );
    
    A_Ss := OrlikSolomonSpacesOfCorankOneOfFlat( matroid, X );
    A_Ts := OrlikSolomonSpacesOfCorankTwoOfFlat( matroid, X );
    
    return MorphismBetweenDirectSumsWithGivenDirectSums( kmat,
                   A_S,
                   A_Ss,
                   List( [ 1 .. Length( Ss ) ], s ->
                         List( [ 1 .. Length( Ts ) ], t ->
                               OrlikSolomonCodifferentialBetweenAPairOfFlatsWithGivenObjects( matroid, Ss[s], Ts[t], A_Ss[s], A_Ts[t] ) ) ),
                   A_Ts,
                   A_T );
    
end );

## ⨁_{T ≤₂ X} A_T ← ⨁_{S ≤₁ X} A_S
InstallMethodWithCache( OrlikSolomonLastButOneCodifferentialOfLocalization,
        [ IsMatroid, IsList ],
        
  function( matroid, X )
    
    return OrlikSolomonLastButOneCodifferentialOfLocalizationWithGivenObjects( matroid, X,
                   DirectSum( kmat, OrlikSolomonSpacesOfCorankOneOfFlat( matroid, X ) ),
                   DirectSum( kmat, OrlikSolomonSpacesOfCorankTwoOfFlat( matroid, X ) ) );
    
end );

## ⨁_{S ≤₁ X} A_S ↩ A_X
InstallMethodWithCache( OrlikSolomonEmbeddingOfSpaceOfFlatWithGivenRange,
        [ IsMatroid, IsList, IsCapCategoryObject ],
        
  function( matroid, X, A_S )
    local rkX, A_T;
    
    rkX := RankFunction( matroid )( X );
    
    if rkX = 0 then
        return UniversalMorphismIntoZeroObject( kmat, TensorUnit( kmat ) );
    elif rkX = 1 then
        return IdentityMorphism( kmat, TensorUnit( kmat ) );
    fi;
    
    A_T := DirectSum( kmat, OrlikSolomonSpacesOfCorankTwoOfFlat( matroid, X ) );
    
    return WeakKernelEmbedding( kmat,
                   OrlikSolomonLastButOneCodifferentialOfLocalizationWithGivenObjects( matroid, X, A_S, A_T ) );
    
end );

## A_X
InstallMethodWithCache( OrlikSolomonSpaceOfFlat,
        [ IsMatroid, IsList ],
        
  function( matroid, X )
    
    return Source( OrlikSolomonEmbeddingOfSpaceOfFlatWithGivenRange( matroid, X, DirectSum( kmat, OrlikSolomonSpacesOfCorankOneOfFlat( matroid, X ) ) ) );
    
end );

## ⨁_{S' ≤₁ X} A_S' → ⨁_{S ≤₁ f(X)} A_S
InstallMethod( OrlikSolomonMorphismBetweenDirectSumOfCorankOneSpacesOfFlatsWithGivenObjects,
        [ IsMatroid, IsMatroid, IsList, IsList, IsCapCategoryObject, IsCapCategoryObject ],
        
  function( source_matroid, target_matroid, X, f, A_source_S, A_target_S )
    local rkX, fX, rkfX, source_Ss, target_Ss, A_source_Ss, A_target_Ss, g;
    
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
    
    A_source_Ss := OrlikSolomonSpacesOfCorankOneOfFlat( source_matroid, X );
    A_target_Ss := OrlikSolomonSpacesOfCorankOneOfFlat( target_matroid, fX );
    
    ##
    A_target_S := DirectSum( kmat, A_target_Ss );
    
    g :=
      function( S_ )
        local fS_, mor;
        
        ## f(S')
        fS_ := Set( f{S_} );
        
        ## A_{S'} → A_{f(S')}
        mor := OrlikSolomonMorphismBetweenSpacesOfFlatsWithGivenObjects( source_matroid, target_matroid, S_, f,
                       OrlikSolomonSpaceOfFlat( source_matroid, S_ ),
                       OrlikSolomonSpaceOfFlat( target_matroid, fS_ ) );
        
        ## f(S') = f(X)?
        if fS_ = fX then
            return PreCompose( kmat,
                           ## here: A_{f(S')} = A_{f(X)}
                           mor,
                           ## ⨁_{S ≤₁ f(X)} A_S ↩ A_{f(X)}
                           OrlikSolomonEmbeddingOfSpaceOfFlatWithGivenRange( target_matroid, fX, A_target_S ) );
        fi;

        return PreCompose( kmat,
                       mor,
                       InjectionOfCofactorOfDirectSumWithGivenDirectSum( kmat,
                               A_target_Ss,
                               SafePosition( target_Ss, fS_ ),
                               A_target_S ) );
        
    end;
    
    return UniversalMorphismFromDirectSumWithGivenDirectSum( kmat,
                   A_source_Ss,
                   A_source_S,
                   List( source_Ss, g ),
                   A_target_S );
    
end );

## A(f): A_X(L') → A_f(X)(L)
InstallMethod( OrlikSolomonMorphismBetweenSpacesOfFlatsWithGivenObjects,
        [ IsMatroid, IsMatroid, IsList, IsList, IsCapCategoryObject, IsCapCategoryObject ],
        
  function( source_matroid, target_matroid, X, f, A_X, A_fX )
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
                   A_X,
                   OrlikSolomonLastButOneCodifferentialOfLocalization( source_matroid, X ),
                   OrlikSolomonMorphismBetweenDirectSumOfCorankOneSpacesOfFlatsWithGivenObjects( source_matroid, target_matroid, X, f,
                           DirectSum( kmat, OrlikSolomonSpacesOfCorankOneOfFlat( source_matroid, X ) ),
                           DirectSum( kmat, OrlikSolomonSpacesOfCorankOneOfFlat( target_matroid, fX ) ) ),
                   OrlikSolomonLastButOneCodifferentialOfLocalization( target_matroid, fX ),
                   A_fX );
    
end );

## A(f): A_X(L') → A_f(X)(L)
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

OrbsL := SortedList( Orbits( W, Concatenation( Flats( L ) ), OnSets ), {a,b} -> Length(a[1]) < Length(b[1]) );
TL := List( OrbsL, O -> O[1] );
StabsL := List( TL, X -> Stabilizer( W, X, OnSets ) );
WsL := List( [ 1 .. Length( TL ) ], k -> Group( List( GeneratorsOfGroup( StabsL[k] ), pi -> EntriesOfHomalgMatrixAsListList( UnderlyingMatrix( OrlikSolomonMorphismBetweenSpacesOfFlats( L, L, TL[k], ListPerm( pi, n ) ) ) ) ) ) );
IndsL := List( [ 1 .. Length( TL ) ], k -> List( ConstituentsOfCharacter( InducedClassFunction( RestrictedClassFunction( NaturalCharacter( WsL[k] ), GroupHomomorphismByImages( StabsL[k], WsL[k] ) ), W ) ), ValuesOfClassFunction ) );
