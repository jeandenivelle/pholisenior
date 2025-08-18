
#ifndef CALC_OPTFORM_
#define CALC_OPTFORM_

#include <optional>
#include <string_view>
#include <iostream>

#include "sequent.h"
#include "errorstack.h"
#include "expander.h"


// An optional formula. 

namespace calc
{
   struct optform
   {
      std::optional< logic::term > fm;

      std::string_view rule; 
      sequent& seq;
      errorstack& err; 

      optform( const std::optional< logic::term > & fm,
               std::string_view rule,
               sequent& seq, errorstack& err )
         : fm( fm ),
           rule( rule ),
           seq( seq ), err( err ) 
      { }

      optform( std::optional< logic::term > && fm,
               std::string_view rule,
               sequent& seq, errorstack& err )
         : fm( std::move( fm )),
           rule( rule ),
           seq( seq ), err( err )
      { } 
           
      void musthave( logic::selector op ); 
      void getsub( size_t ind );
      void getuniquesub( );
      void aritymustbe( size_t i );  // Works for Kleene operators only.
      void make_anf2( );
      void normalize( );
      void expand( expander& def ); 

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

