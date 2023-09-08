LoadPackage( "alcove", ">= 2023.09-02" );
LoadPackage( "LinearAlgebraForCAP" );
LoadPackage( "FinSetsForCAP" );

Q := HomalgFieldOfRationals( );

Qmat := MatrixCategory( Q );

BooleanArrangement :=
  function( r )
    local id;
    
    id := HomalgIdentityMatrix( r, Q );
    
    return Matroid( id );
    
end;

BraidArrangement :=
  function( r )
    local id, z, j, pair;
    
    id := HomalgIdentityMatrix( r, Q );
    
    z := HomalgInitialMatrix( r, Binomial( r, 2 ), Q );
    
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
        
        return ZeroMorphism( Qmat,
                       A_X,
                       A_S );
        
    fi;
    
    A_Ss := OrlikSolomonSpacesOfCorankOneOfFlat( matroid, X );
    
    return ComponentOfMorphismIntoDirectSum( Qmat,
                   OrlikSolomonEmbeddingOfSpaceOfFlatWithGivenRange( matroid, X, DirectSum( Qmat, A_Ss ) ),
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
    
    return MorphismBetweenDirectSumsWithGivenDirectSums( Qmat,
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
                   DirectSum( Qmat, OrlikSolomonSpacesOfCorankOneOfFlat( matroid, X ) ),
                   DirectSum( Qmat, OrlikSolomonSpacesOfCorankTwoOfFlat( matroid, X ) ) );
    
end );

## ⨁_{S ≤₁ X} A_S ↩ A_X
InstallMethodWithCache( OrlikSolomonEmbeddingOfSpaceOfFlatWithGivenRange,
        [ IsMatroid, IsList, IsCapCategoryObject ],
        
  function( matroid, X, A_S )
    local rkX, A_T;
    
    rkX := RankFunction( matroid )( X );
    
    if rkX = 0 then
        return UniversalMorphismIntoZeroObject( Qmat, TensorUnit( Qmat ) );
    elif rkX = 1 then
        return IdentityMorphism( Qmat, TensorUnit( Qmat ) );
    fi;
    
    A_T := DirectSum( Qmat, OrlikSolomonSpacesOfCorankTwoOfFlat( matroid, X ) );
    
    return KernelEmbedding( Qmat,
                   OrlikSolomonLastButOneCodifferentialOfLocalizationWithGivenObjects( matroid, X, A_S, A_T ) );
    
end );

## A_X
InstallMethodWithCache( OrlikSolomonSpaceOfFlat,
        [ IsMatroid, IsList ],
        
  function( matroid, X )
    
    return Source( OrlikSolomonEmbeddingOfSpaceOfFlatWithGivenRange( matroid, X, DirectSum( Qmat, OrlikSolomonSpacesOfCorankOneOfFlat( matroid, X ) ) ) );
    
end );

## ⨁_{S' ≤₁ X} A_S' → ⨁_{S ≤₁ f(X)} A_S
InstallMethod( OrlikSolomonMorphismBetweenDirectSumOfCorankOneSpacesOfFlatsWithGivenObjects,
        [ IsMatroid, IsMatroid, IsList, IsList, IsCapCategoryObject, IsCapCategoryObject ],
        
  function( source_matroid, target_matroid, X, f, A_source_S, A_target_S )
    local rkX, fX, rkfX, source_Ss, target_Ss, A_source_Ss, A_target_Ss, g;
    
    rkX := RankFunction( source_matroid )( X );
    
    if rkX = 0 then
        return IdentityMorphism( Qmat, TensorUnit( Qmat ) );
    elif rkX = 1 then
        return IdentityMorphism( Qmat, TensorUnit( Qmat ) );
    fi;
    
    ## f(X)
    fX := Set( f{X} );
    
    rkfX := RankFunction( target_matroid )( fX );
    
    source_Ss := OrlikSolomonFlatsOfCorankOneOfFlat( source_matroid, X );
    target_Ss := OrlikSolomonFlatsOfCorankOneOfFlat( target_matroid, fX );
    
    A_source_Ss := OrlikSolomonSpacesOfCorankOneOfFlat( source_matroid, X );
    A_target_Ss := OrlikSolomonSpacesOfCorankOneOfFlat( target_matroid, fX );
    
    ##
    A_target_S := DirectSum( Qmat, A_target_Ss );
    
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
            return PreCompose( Qmat,
                           ## here: A_{f(S')} = A_{f(X)}
                           mor,
                           ## ⨁_{S ≤₁ f(X)} A_S ↩ A_{f(X)}
                           OrlikSolomonEmbeddingOfSpaceOfFlatWithGivenRange( target_matroid, fX, A_target_S ) );
        fi;

        return PreCompose( Qmat,
                       mor,
                       InjectionOfCofactorOfDirectSumWithGivenDirectSum( Qmat,
                               A_target_Ss,
                               SafePosition( target_Ss, fS_ ),
                               A_target_S ) );
        
    end;
    
    return UniversalMorphismFromDirectSumWithGivenDirectSum( Qmat,
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
        return IdentityMorphism( Qmat, TensorUnit( Qmat ) );
    elif rkX = 1 then
        return IdentityMorphism( Qmat, TensorUnit( Qmat ) );
    fi;
    
    ## f(X)
    fX := Set( f{X} );
    
    return KernelObjectFunctorialWithGivenKernelObjects( Qmat,
                   A_X,
                   OrlikSolomonLastButOneCodifferentialOfLocalization( source_matroid, X ),
                   OrlikSolomonMorphismBetweenDirectSumOfCorankOneSpacesOfFlatsWithGivenObjects( source_matroid, target_matroid, X, f,
                           DirectSum( Qmat, OrlikSolomonSpacesOfCorankOneOfFlat( source_matroid, X ) ),
                           DirectSum( Qmat, OrlikSolomonSpacesOfCorankOneOfFlat( target_matroid, fX ) ) ),
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
A4 := BraidArrangement( 4 );
n := Length( GroundSet( A4 ) );
rkA4 := RankFunction( A4 );
muA4 := MoebiusFunction( A4 );
WA4 := AutomorphismGroup( A4 );

Assert( 0, ForAll( Concatenation( Flats( A4 ) ), X -> Dimension( OrlikSolomonSpaceOfFlat( A4, X ) ) = AbsInt( muA4( X ) ) ) );
Assert( 0, ForAll( Concatenation( Flats( A4 ) ), X -> Dimension( Source( OrlikSolomonMorphismBetweenSpacesOfFlats( A4, A4, X, GroundSet( A4 ) ) ) ) = AbsInt( muA4( X ) ) ) );

OrbsA4 := SortedList( Orbits( WA4, Concatenation( Flats( A4 ) ), OnSets ), {a,b} -> Length(a[1]) < Length(b[1]) );
TA4 := List( OrbsA4, O -> O[1] );
StabsA4 := List( TA4, X -> Stabilizer( WA4, X, OnSets ) );
