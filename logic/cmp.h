
// Written by Akhmetzhan Kussainov and Hans de Nivelle Spring 2023.
// Revised in August 2024 by Hans de Nivelle. 
// Almost completely rewritten in August 2025 by Hans de Nivelle.
// I removed Knuth-Bendix order, and replaced it by just equality.


#ifndef LOGIC_CMP_
#define LOGIC_CMP_ 

#include <iostream>

#include "term.h"

namespace logic
{

   namespace cmp
   {
      using weight_t = uint_least64_t; 

      weight_t weight( const type& tp );
      weight_t weight( const term& t );
  
      bool equal( const type& tp1, const type& tp2 );
      bool equal( const term& tm1, const term& tm2 );

   }

}

#endif

