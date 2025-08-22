
#ifndef CALC_FORMULASET_
#define CALC_FORMULASET_

#include <vector>
#include <iostream>

#include "logic/term.h"

namespace calc
{
   // Implementation is very simple. All basic operations are linear.
   // Hans de Nivelle, 2025.08.22.

   class formulaset
   {
      std::vector< logic::term > repr; 
         // This is actually a very inefficient O(n^2) representation,
         // but I expect that formula sets will never be big.

   public:
      formulaset( ) noexcept = default;

      bool contains( const logic::term& fm ) const; 
         // O(n).

      bool insert( const logic::term& fm );
      bool insert( logic::term&& fm );

      void sort_increasing( );
         // Sort by increasing size. This is also very inefficient O(n^2). 
         // We don't exchange formulas with same size.

      using const_iterator = std::vector< logic::term > :: const_iterator;

      const_iterator begin( ) const { return repr. begin( ); }
      const_iterator end( ) const { return repr. end( ); }
      size_t size( ) const { return repr. size( ); }
 
      void print( std::ostream& out ) const;     
   };
}

#endif

