
#ifndef LOGIC_REPLACEMENTS_
#define LOGIC_REPLACEMENTS_   

#include "term.h"
#include "topdown.h"
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


   // A vector substitution assigns values to all
   // De Bruijn indices from #0 to #(s-1). 
   // Because of this, it can be represented by a 
   // vector of values. vector_subst supports 
   // stack-like behaviour. This is needed for
   // anti-prenexing.

   struct vector_subst 
   {
      std::vector< term > values; 

      vector_subst( ) = default; 
         // You may add the values by yourself.
         // I don't know where they come form. 
         // I have no wish to make a polymorphic constructor. 

      void push( const term& t ) { values. push_back(t); }
      void push( term&& t ) { values. push_back( std::move(t)); }

      size_t size( ) const { return values. size( ); }
      void restore( size_t s );

      term operator( ) ( term t, size_t vardepth, bool& change ) const;

      void print( std::ostream& out ) const;
   };


   // A sparse subst assigns values to some, but not
   // necessarily all, De Bruijn indices. 

   class sparse_subst
   {
      std::unordered_map< size_t, term > repl;

   public:
      sparse_subst( ) noexcept = default;

      void assign( size_t var, const term& val )
         { repl. insert( std::pair( var, val )); }
      void assign( size_t var, term&& val )
         { repl. insert( std::pair( var, std::move( val ))); }

      term operator( ) ( term t, size_t vardepth, bool& change ) const;
 
      void print( std::ostream& out ) const;      
   };


   struct betareduction 
   {
      betareduction( ) = default;

      term operator( ) ( term t, size_t vardepth, bool& change ) const;

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

   
   struct definition
   {
      exact id;
      term val;
      
      definition( exact id, const term& val )
         : id(id), val( val )
      { }

      term operator( ) ( const term& t, size_t vardepth ) const; 

      void print( std::ostream& out ) const;
   };

   struct projection
   {



   };
}

#endif 


