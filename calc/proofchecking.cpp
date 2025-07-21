
#include "proofchecking.h"

#include "removelets.h"
#include "alternating.h"

#include "logic/pretty.h"
#include "logic/replacements.h"

const logic::term&
calc::get_conjunct( const logic::term& fm, size_t ind, errorstack& err )
{
   if( fm. sel( ) != logic::op_kleene_and )
   {
      err. push( "formula is not a Kleene-and" );
      throw failure( );
   }

   if( ind >= fm. view_kleene( ). size( ))
   {
      errorstack::builder bld;
      bld << "conjunction does not have " << ind << "-th conjunct";
      err. push( std::move( bld ));
      throw failure( );
   }

   return fm. view_kleene( ). sub( ind ); 
}


const logic::term&
calc::get_disjunct( const logic::term& fm, size_t ind, errorstack& err )
{
   if( fm. sel( ) != logic::op_kleene_or )
   {
      err. push( "formula is not a Kleene-or" );
      throw failure( ); 
   }        
         
   if( ind >= fm. view_kleene( ). size( ))
   {     
      errorstack::builder bld;
      bld << "disjunction does not have " << ind << "-th disjunct";
      err. push( std::move( bld ));
      throw failure( );
   }  
   
   return fm. view_kleene( ). sub( ind );
}        
      

bool
calc::iscontradiction( const logic::term& fm )
{
   std::cout << "is this a contradiction " << fm << " ??\n";

}


logic::term 
calc::eval( const proofterm& prf, sequent& seq, errorstack& err )
{
   std::cout << "evaluating " << prf << "\n";

   switch( prf. sel( ))
   {
   case prf_truthconst:
      return logic::term( logic::op_kleene_and,
                             std::initializer_list< logic::term > ( ));
   case prf_exact:
      {
         auto ex = prf. view_exact( ). exact( );
         return seq. getformula( ex ); 
      }

   case prf_ident:
      {
         auto id = prf. view_ident( ). ident( );
         const auto& f = seq. blfs. getformulas( id ); 
         if( f. empty( ))
            throw std::logic_error( "not found" );
         if( f. size( ) > 1 )
            throw std::logic_error( "too many" ); 

         return seq. getformula( f. front( ));
      }

   case prf_clausify:
      {
         auto cl = prf. view_clausify( ); 
         auto fm = eval( cl. parent( ), seq, err );
         logic::context ctxt;  
         fm = removelets( seq, ctxt, fm );
         if( ctxt. size( ))
            throw std::logic_error( "context not empty" ); 

         fm = alternating( fm, logic::op_kleene_and, 2 );
         return fm;    
      }
   
   case prf_resolve:
      {
         size_t nrerrors = err. size( );
         auto res = prf. view_resolve( ); 
         auto par = eval( res. parent( ), seq, err );
         std::cout << "parent = " << par << "\n";

         try
         {
            auto conj = get_conjunct( par, res. conj( ), err );
            std::cout << "selected conjuct = " << conj << "\n";

            logic::term disj = get_disjunct( conj, res. disj( ), err );
            std::cout << "selected disjunct = " << disj << "\n";

            // They cannot be repeated, but a while is as easy
            // to write as an if:

            logic::fullsubst namesubst; 
               // We need to substitute global names instead
               // of De Bruijn indices.

            while( disj. sel( ) == logic::op_kleene_exists )
            {
               auto ex = disj. view_quant( );
               for( size_t i = 0; i != ex. size( ); ++ i )
               {
                  logic::exact name = 
                     seq. assume( ex. var(i). pref, ex. var(i). tp );

                  namesubst. push( logic::term( logic::op_exact, name ));
               }

               disj = ex. body( ); 
            }

            std::cout << namesubst << "\n";
            bool dontcare = false;
            disj = topdown( namesubst, std::move( disj ), 0, dontcare );

            seq. assume( res. name( ), disj ); 
            std::cout << seq << "\n";
            std::cout << disj << "\n";
         }
         catch( failure f )
         {
            std::cout << "caught the failure in first part\n"; 
            throw std::logic_error( "take action" );
         }

         auto first = eval( res. first( ), seq, err );
         std::cout << "first = " << first << "\n";
         if( !iscontradiction( first ))
            throw std::logic_error( "not a contradition" );

         
      }   
      throw std::logic_error( "not finished" );

   case prf_unfinished:
      {
         errorstack::builder bld;
         bld << "Using The Unfinished Rule:\n";
         auto unf = prf. view_unfinished( ); 
         for( size_t i = 0; i != unf. size( ); ++ i )
         {
            bld << i << " : "; 
            bld << eval( unf. show(i), seq, err ) << "\n";
         }
         err. push( std::move( bld ));
      }
      return logic::term( logic::op_kleene_and, {
                logic::term( logic::op_kleene_or, { } ) } );
   }

   std::cout << prf. sel( ) << "\n";
   throw std::logic_error( "dont know how to check proof term" );
}



