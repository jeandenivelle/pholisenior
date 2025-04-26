
#ifndef SEMANTICS_INTERPRETATION_
#define SEMANTICS_INTERPRETATION_

#include <iostream>
#include <vector>
#include <unordered_map>

#include "logic/term.h"
#include "logic/selector.h"
#include "function.h"

namespace semantics 
{
   namespace lattice
   {
      value top( logic::selector sel );
      value bottom( logic::selector sel );

      value merge( logic::selector sel, value val1, value val2 );
         // Always towards the bottom. 
   }

   // An identifier with a type:

   struct identtype
   {
      identifier id;
      logic::type tp;

      identtype( ) = delete;
      identtype( const identifier& id, const logic::type& tp )
         : id( id ), tp( tp )
      { }

      void print( std::ostream& out ) const
         { out << id << ": " << tp; } 

   };


   struct interpretation
   {
      unsigned int nrobjects;   // Number of objects in domain. 

      std::unordered_map< identifier, function, 
                          identifier::hash, identifier::equal_to > mp;

      std::vector< function > valuation;

      interpretation( unsigned int nrobjects ) 
         : nrobjects( nrobjects )
      { }

      size_t nr_identifiers( ) const { return mp. size( ); }

      function& extend( identifier id, function&& f )
      { 
         auto p = mp. emplace( id, std::move(f));
         if( !p. second ) 
            throw std::logic_error( "extend: identifier is present" );
         return p. first -> second; 
      }

      void retract( identifier id ) 
      { 
         if( !mp. erase( id ))
            throw std::logic_error( "retract: identifier not present" );
      }

      const function& at( identifier id ) const { return mp. at( id ); }

      const function& local( size_t ind ) const 
      { 
         if( ind >= valuation. size( ))
             throw std::out_of_range( "bad De Bruijn index" );
         return valuation[ valuation. size( ) - ind - 1 ]; 
      }
 
      function& push( function&& f )
         { valuation. push_back( std::move(f) ); return valuation. back( ); }

      void pop( ) { valuation. pop_back( ); }

      void print( std::ostream& out ) const; 
   };

   function zero_function( logic::type tp, unsigned int nrobjects );

         
   value eval( interpretation& interpr, const logic::term& t );

   void
   update_quant( value& val, const value& worst,
                 interpretation& interpr, 
                 const logic::term& quant, size_t ind ); 
      // quant must be a quantified formula. 
      // ind is the variable that we are currently looking at. 
      // We give up when val becomes the worst possible value.

   const function& eval_func( interpretation& interpr, const logic::term& t );

   void 
   check_preceq( std::vector< identtype > :: const_iterator id1,
                 std::vector< identtype > :: const_iterator id2,  
                 const logic::term& from, const logic::term& into,
                 interpretation& interpr );

   void 
   check_preceq( const std::vector< identtype > & idents, 
                 const logic::term& from, const logic::term& into ); 
}

#endif

