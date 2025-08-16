
#ifndef CALC_OPTFORM_
#define CALC_OPTFORM_

#include <optional>
#include <string_view>
#include <iostream>

#include "sequent.h"
#include "errorstack.h"

// An optional formula. 

namespace calc
{
   struct optform
   {
      std::optional< logic::term > fm;

      std::string_view rule; 
      const sequent& seq;
      errorstack& err; 

      optform( const std::optional< logic::term > & fm,
               std::string_view rule,
               const sequent& seq, 
               errorstack& err )
         : fm( fm ),
           rule( rule ),
           seq( seq ),
           err( err ) 
      { }

      void musthave( logic::selector op ); 
      void getsub( size_t ind );
      void getuniquesub( );

      bool has_value( ) const { return fm. has_value( ); }
      const logic::term& value( ) const { return fm. value( ); }
      logic::term& value( ) { return fm. value( ); }

      errorstack::builder errorheader( );
         // Not const, because we are pretending that we own err.

      void print( std::ostream& out ) const;
      void pretty( std::ostream& out ) const;

      static const char* pretty( logic::selector op ); 
   };
}

#endif

