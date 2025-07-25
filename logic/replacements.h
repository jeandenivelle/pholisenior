
#ifndef LOGIC_REPLACEMENTS_
#define LOGIC_REPLACEMENTS_   

#include "term.h"
#include "outermost.h"
#include "util/print.h"

#include <vector>
#include <unordered_map>

namespace logic
{
   // Either return a very_equal term (in simple cases 'the same term'), 
   // or a replacement.
   // The boolean should be assignend true when a replacement happened, 
   // and not changed when there was no replacement. 

   struct lifter
   {
      size_t dist;

      lifter( ) = delete;

      explicit lifter( size_t dist )
         : dist( dist )
      { }

      term operator( ) ( term t, size_t vardepth, bool& change ) const;

      void print( std::ostream& out ) const; 
   };


   // A sparse subst assigns values to some, but not
   // necessarily all, De Bruijn indices. 
   // Variables that are not in the domain of the substitution,
   // are not changed.

   class sparse_subst
   {
      std::unordered_map< size_t, term > repl;

   public:
      sparse_subst( ) noexcept = default;
      sparse_subst( sparse_subst&& ) noexcept = default;
      sparse_subst& operator = ( sparse_subst&& ) = default;

      void assign( size_t var, const term& val )
         { repl. insert( std::pair( var, val )); }
      void assign( size_t var, term&& val )
         { repl. insert( std::pair( var, std::move( val ))); }

      term operator( ) ( term t, size_t vardepth, bool& change ) const;
 
      void print( std::ostream& out ) const;      
   };


   // A single subst replaces #0 by value. 

   struct singlesubst
   {
      term value; 

      singlesubst( const term& value ) 
         : value( value ) 
      { }

      term operator( ) ( term t, size_t vardepth, bool& change ) const;
      void print( std::ostream& out ) const;
   };
    
   // A fullsubst completely removes the nearest DeBruijn indices 
   // #0,#1,#2, ... 
   // DeBruijn that are not in the fullsubst are shifted down. 

   class fullsubst
   {
      std::vector< term > values;

   public:
      fullsubst( ) noexcept
      { }

      fullsubst( std::vector< term > && values ) noexcept
         : values( std::move( values ))
      { }

      term operator( ) ( term t, size_t vardepth, bool& change ) const;

      void print( std::ostream& out ) const;

      size_t size( ) const { return values. size( ); } 
      void push( term&& val ) { values. push_back( std::move( val )); }
   };

   // Argument substitution works like fullsubst, but it uses
   // the arguments of an application term. 
   // If you have a beta-redux 
   // apply( lambda ( T1, ..., Tn ) t, u1 ... um ), 
   // there is no need to construct fullsubst( u1, ..., um ).
   // Instead one can use the application term to get the ui.

   struct argsubst
   {
      term argterm;    // Term from which we take the arguments.
      size_t arity;    // In case of incomplete application, 
                       // we don't use all arguments of argterm.

      argsubst( const term& argterm, size_t arity )
         : argterm( argterm ),
           arity( arity )
      { }

      term operator( ) ( term t, size_t vardepth, bool& change ) const;

      void print( std::ostream& out ) const;
   };


   // This is incomplete beta-reduction:

   struct betareduction 
   {
      size_t counter; 

      betareduction( ) noexcept
         : counter(0) 
      { }

      term operator( ) ( term t, size_t vardepth, bool& change );
         // Not const, because we count the reductions.

      void print( std::ostream& out ) const; 
   };


   struct equalitysystem
   {
      std::vector< std::pair< term, term >> sys;

      equalitysystem( ) = default;

      // Use const& or move:

      equalitysystem( const std::vector< std::pair< term, term >> & sys )
         : sys( sys )
      { }

      equalitysystem( std::vector< std::pair< term, term >> && sys )
         : sys( std::move( sys ))
      { }

      term operator( ) ( const term& t, size_t vardepth ) const;

      void print( std::ostream& out ) const;
   };

}

#endif 


