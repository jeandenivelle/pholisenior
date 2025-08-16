
#include "proofchecking.h"

#include "removelets.h"
#include "alternating.h"
#include "expander.h"
#include "projection.h"

#include "logic/pretty.h"
#include "logic/replacements.h"
#include "logic/structural.h"

errorstack::builder
calc::errorheader( const sequent& seq, std::string_view rule )
{
   errorstack::builder bld;
   for( unsigned int i = 0; i < 60; ++ i )
      bld. put( '-' );
   bld. put( '\n' );

   bld << "Error applying " << rule << ":\n";
   bld << seq << "\n";
   return bld;
}

void 
calc::print( std::ostream& out, const sequent& seq, const logic::term& tm )
{
   logic::context ctxt;
   logic::pretty::print( out, seq. blfs, ctxt, tm );
}

void calc::print( std::ostream& out, logic::selector op )
{
   switch( op )
   {
   case logic::op_kleene_or:
      out << "kleene-or"; return;  
   case logic::op_kleene_and:
      out << "kleene-and"; return;
   case logic::op_kleene_forall:
      out << "kleene-forall"; return;
   case logic::op_kleene_exists:
      out << "kleene-exists"; return;
   }
   out << "???";
}

bool calc::operatorcorrect( logic::selector op, 
                            const logic::term& fm, const sequent& seq, 
                            std::string_view rule, errorstack& err )
{
   if( fm. sel( ) == op )
      return true; 

   errorstack::builder bld;
   bld << "wrong operator for " << rule << " : ";
   bld << "operator must be ";
   print( bld, op ); 
   bld << ", but the formula is: ";
   print( bld, seq, fm );
   err. push( std::move( bld ));

   return false; 
}


std::optional< logic::term > 
calc::subform( const logic::term& fm, size_t i, const sequent& seq, 
               std::string_view rule, errorstack& err )
{
   if( !fm. option_is_kleene( ))
      throw std::logic_error( "subform: Not a Kleene operator" ); 

   if( i >= fm. view_kleene( ). size( ))
   {
      auto bld = errorheader( seq, rule ); 
      bld << "need subform nr " << i << ", but there are only ";
      bld << fm. view_kleene( ). size( ) << " in: ";
      print( bld, seq, fm );
      err. push( std::move( bld )); 
      return { };
   }

   return fm. view_kleene( ). sub(i); 
}

std::optional< logic::term >
calc::uniquesubform( const logic::term& fm, const sequent& seq,
                     std::string_view rule, errorstack& err )
{
   if( fm. sel( ) == logic::op_kleene_or )
   {
      auto kl = fm. view_kleene( );
      if( kl. size( ) == 1 )
         return kl. sub(0);
   }

   auto bld = errorheader( seq, rule );
   bld << "formula must a disjunction of arity one, but it is :";
   print( bld, seq, fm );
   err. push( std::move( bld ));
   return { };
}

logic::term
calc::replace( logic::term fm, size_t i, const logic::term& val )
{
   if( !fm. option_is_kleene( ))
      throw std::logic_error( "replace: Not a Kleene operator" ); 

   if( i >= fm. view_kleene( ). size( )) 
      throw std::logic_error( "replace: index too big" );

   fm. view_kleene( ). update_sub( i, val ); 
   return fm; 
}

logic::term
calc::remove( logic::term fm, size_t i )
{
   if( !fm. option_is_kleene( )) 
      throw std::logic_error( "remove: Not a Kleene operator" );

   auto kl = fm. view_kleene( );
   if( i >= kl. size( ))
      throw std::logic_error( "remove: index too big" );

   while( i + 1 < kl. size( ))
   {
      kl. update_sub( i, kl. extr_sub( i + 1 ));
      ++ i;
   }

   kl. pop_back( );
   return fm;
}


logic::term
calc::normalize( const logic::beliefstate& blfs, logic::term tm )
{
   logic::betareduction beta;
   projection proj( blfs ); 

   do 
   {
      beta. counter = 0;
      tm = outermost( beta, std::move( tm ), 0 );
   }
   while( beta. counter );
   return tm;
}

bool
calc::iscontradiction( const logic::term& fm )
{
   switch( fm. sel( ))
   {
   case logic::op_kleene_and:
      {
         auto conj = fm. view_kleene( );
         for( size_t i = 0; i != conj. size( ); ++ i )
         {
            if( iscontradiction( conj. sub(i)))
               return true;
         }
         return false; 
      }
   
   case logic::op_kleene_or:
      {
         auto disj = fm. view_kleene( );
         for( size_t i = 0; i != disj. size( ); ++ i )
         {
            if( !iscontradiction( disj. sub(i)))
               return false;
         }
         return true;
      }

   case logic::op_kleene_exists:
      {
         auto quant = fm. view_quant( ); 
         return iscontradiction( quant. body( ));
      }
   }

   return false;
}


std::optional< logic::term >
calc::deduce( const proofterm& prf, sequent& seq, errorstack& err )
{
   std::cout << "deducing result of term\n";
   prf. print( indentation( ), std::cout ); 
   std::cout << "\n";

   switch( prf. sel( ))
   {

#if 0
   case prf_exact:
      {
         auto ex = prf. view_exact( ). exact( );
         return seq. getformula( ex, err ); 
      }
#endif

   case prf_ident:
      {
         auto id = prf. view_ident( ). ident( );
         const auto& f = seq. blfs. getformulas( id ); 
         if( f. empty( ))
         {
            errorstack::builder bld;
            bld << "unknown identifier " << id << " was used in a proof";
            err. push( std::move( bld ));
            return { };
         }

         if( f. size( ) > 1 )
         {
            errorstack::builder bld; 
            bld << "ambiguous identifier " << id << " was used in a proof";
            err. push( std::move( bld ));
            return { };
         }

         return seq. getformula( f. front( ), err );
      }

   case prf_clausify:
      {
         auto cl = prf. view_clausify( ); 
         auto fm = deduce( cl. parent( ), seq, err );
         if( !fm. has_value( ))
            return { };

         logic::context ctxt;  
         fm. value( ) = removelets( seq, ctxt, fm. value( ));
         if( ctxt. size( ))
            throw std::logic_error( "context not empty" ); 

         fm. value( ) = alternating( fm. value( ), logic::op_kleene_and, 2 );
         return fm;    
      }

   case prf_disjelim:
      {
         size_t nrerrors = err. size( );
         size_t seqsize = seq. size( );

         auto elim = prf. view_disjelim( ); 
         auto conj = deduce( elim. parent( ), seq, err );

         if( !conj. has_value( ))
            return conj;
 
         std::cout << conj. value( ) << "\n";
         if( !operatorcorrect( logic::op_kleene_and, conj. value( ), 
                               seq, "disj-elim", err ))
         {
            return {};
         }

         auto disj = subform( conj. value( ), elim. nrdisj( ), 
                     seq, "disj-elim", err );

         if( !disj. has_value( ))
            return disj;

         std::cout << disj. value( ) << "\n";

         if( !operatorcorrect( logic::op_kleene_or, disj. value( ),
                               seq, "disj-elim", err ))
         {
            return { };
         }

         auto kl = disj. value( ). view_kleene( );

         if( kl. size( ) != elim. size( ))
         {
            auto bld = errorheader( seq, "disj-elim" );
            bld << "disjunction has wrong arity: It is " << kl. size( );
            bld << ", but it must be " << elim. size( ) << "\n";
            print( bld, seq, disj. value( ));
            err. push( std::move( bld ));
            return { }; 
         }

         for( size_t i = 0; i != kl. size( ); ++ i )
         {
            seq. assume( elim. name(i), kl. sub(i));
 
#if 0 
         {
            logic::fullsubst namesubst; 
               // We need to substitute global names in place of 
               // of the DeBruijn indices.

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

            disj = outermost( namesubst, std::move( disj ), 0 );
         }

         seq. assume( res. name( ), disj ); 
         std::cout << seq << "\n";
         std::cout << "disj = " << disj << "\n";

         auto first = deduce( res. first( ), seq, err );
         if( !iscontradiction( first ))
            throw std::logic_error( "not a contradiction" );

         seq. restore( seqsize ); 
         std::cout << seq << "\n";

         auto rest = remove( subform( parent, res. conj( )), res. disj( ));
         return replace( parent, res. conj( ), rest );
#endif
         throw std::logic_error( "disj-elim is unfinished" );
         }
      }

#if 0
   case prf_expand:
      {
         auto exp = prf. view_expand( ); 
         logic::term parent = deduce( exp. parent( ), seq, err ); 
         expander def( exp. ident( ), exp. occ( ), seq. blfs, err );
         std::cout << def << "\n"; 
         parent = outermost( def, std::move( parent ), 0 );
         std::cout << parent << "\n";
         parent = normalize( seq. blfs, parent );
         std::cout << "expander becomes " << def << "\n";
         return parent; 
      }

   case prf_define: 
      {
         auto def = prf. view_define( );
         size_t seqsize = seq. size( );
         
         // We need to type check the value:

         auto val = def. val( );
         size_t errsize = err. size( );
         logic::context ctxt;
         auto tp = checkandresolve( seq. blfs, err, ctxt, val );

         if( err. size( ) > errsize )
         {
            err. addheader( errsize, "during type checking of inproof definition" );
            throw failure( ); 
         } 

         if( !tp. has_value( ))
            throw std::logic_error( "should be unreachable" );

         seq. define( def. name( ), val, tp. value( ));
         auto res = deduce( def. parent( ), seq, err );
         std::cout << "YOU NEED TO CHECK THAT IDENTIFIER DOES NOT OCCUR IN FORMULA";
         std::cout << "(just substitute it away)\n";
         seq. restore( errsize );
         return res;
      }
#endif

   case prf_existselim:
      {
         size_t seqsize = seq. size( );

         auto elim = prf. view_existselim( );
         auto conj = deduce( elim. parent( ), seq, err );

         if( !conj. has_value( ))
            return conj;

         auto exists = optform( conj, "exists-elim", seq, err );
         exists. musthave( logic::op_kleene_and ); 
         exists. getsub( elim. nrexists( ));
         exists. musthave( logic::op_kleene_or );
         exists. getuniquesub( );
         exists. musthave( logic::op_kleene_exists );

         if( !exists. has_value( ))
            return { };

         // At this point, we are sure that existselim can be applied:

         {
            logic::fullsubst namesubst;
               // We need to substitute global names in place of
               // of the DeBruijn indices.

            while( exists. value( ). sel( ) == logic::op_kleene_exists )
            {
               auto ex = exists. value( ). view_quant( );
               for( size_t i = 0; i != ex. size( ); ++ i )
               {
                  logic::exact name =
                     seq. assume( ex. var(i). pref, ex. var(i). tp );

                  namesubst. push( logic::term( logic::op_exact, name ));
               }

               exists. value( ) = ex. body( );
            }

            exists. value( ) = 
               outermost( namesubst, std::move( exists. value( )), 0 );

         }

         seq. assume( elim. name( ), exists. value( ));

         std::cout << seq << "\n";
         std::cout << "exists = " << exists << "\n";

#if 0
         auto first = deduce( res. first( ), seq, err );
         if( !iscontradiction( first ))
            throw std::logic_error( "not a contradiction" );

         seq. restore( seqsize );
         std::cout << seq << "\n";

         auto rest = remove( subform( parent, res. conj( )), res. disj( ));
         return replace( parent, res. conj( ), rest );
#endif
         throw std::logic_error( "exists-elim is not implemented" );

      }

#if 0
   case prf_forallelim:
      {
         size_t nrerrors = err. size( );
         size_t seqsize = seq. size( );

         auto elim = prf. view_forallelim( );


      }

   case prf_unfinished:
      {
         errorstack::builder bld;
         bld << "--------------------------------------------------\n";
         bld << "Unfinished Proof:\n";
         bld << seq << "\n";
         auto unf = prf. view_unfinished( ); 
         bld << "Formulas:\n";
         for( size_t i = 0; i != unf. size( ); ++ i )
         {
            logic::context ctxt; 
            bld << "   " << i << " : "; 
            logic::pretty::print( bld, seq. blfs, ctxt, deduce( unf. show(i), seq, err ));
         }
         err. push( std::move( bld ));
      }
      return logic::term( logic::op_kleene_and, {
                logic::term( logic::op_kleene_or, { } ) } );
#endif

   }

   std::cout << prf. sel( ) << "\n";
   throw std::logic_error( "dont know how to check proof term" );
}


