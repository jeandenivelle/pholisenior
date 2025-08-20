
#include "proofchecking.h"

#include "logic/pretty.h"
#include "logic/replacements.h"
#include "logic/structural.h"
#include "logic/cmp.h"


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
   std::cout << "deducing result of proof term\n";
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

         auto res = optform( std::move( fm ), "clausify", seq, err );
         res. make_anf2( );
         return res. value( );
      }

   case prf_orelim:
      {

         auto elim = prf. view_orelim( ); 
         auto conj = deduce( elim. parent( ), seq, err );

         if( !conj. has_value( ))
            return conj;

         auto disj = optform( std::move( conj ), "or-elim", seq, err );
         disj. musthave( logic::op_kleene_and );
         disj. getsub( elim. nror( ));
         disj. musthave( logic::op_kleene_or );
         disj. aritymustbe( elim. size( ));
         if( !disj. has_value( ))
            return { };
         std::cout << "we are not here\n";
         std::cout << disj << "\n";
 
         auto kl = disj. value( ). view_kleene( );
         size_t seqsize = seq. size( );

         for( size_t i = 0; i != kl. size( ); ++ i )
         {
            {
               auto sub = optform( kl. sub(i), "or-elim", seq, err );
               sub. make_anf2( );
               seq. assume( elim. name(i), sub. value( ));
            }

            auto sub = optform( deduce( elim. branch(i), seq, err ),
                                "result of or-elim", seq, err );
                            
            std::cout << "or-elim got back:\n";
            std::cout << sub << "\n"; 
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
            seq. restore( seqsize );

            std::cout << seq << "\n";
         }
         throw std::logic_error( "or-elim is unfinished" );
      }

   case prf_expand:
      {
         auto exp = prf. view_expand( ); 
         auto parent = deduce( exp. parent( ), seq, err ); 
         if( !parent. has_value( ))
            return { };

         auto nm = optform( std::move( parent ), "expand", seq, err );

         expander def( exp. ident( ), exp. occ( ), seq. blfs, err );
            // We are using unchecked identifier exp. ident( ).
            // The expander will look only at exact overloads. 
            // This guarantees type safety.

         std::cout << def << "\n"; 

         nm. expand( def ); 
         nm. normalize( );
         // nm. make_anf2( );
         std::cout << "expand returns " << nm << "\n";
         return nm. value( );
      }

   case prf_define: 
      {
         auto def = prf. view_define( );
         
         // We first need to typecheck the value:

         auto val = def. val( );
         size_t errsize = err. size( );
         logic::context ctxt;
         auto tp = checkandresolve( seq. blfs, err, ctxt, val );

         if( err. size( ) > errsize )
         {
            err. addheader( errsize, "during type checking of inproof definition" );
            throw std::logic_error( "do something" );
         } 

         if( !tp. has_value( ))
            throw std::logic_error( "should be unreachable" );

         size_t seqsize = seq. size( );
         seq. define( def. name( ), val, tp. value( ));

         auto res = deduce( def. parent( ), seq, err );

         std::cout << "YOU NEED TO CHECK THAT IDENTIFIER DOES NOT OCCUR IN FORMULA";
         std::cout << "(just substitute it away)\n\n";
         seq. restore( seqsize );
         return res;
      }

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

         exists. make_anf2( );

         seq. assume( elim. name( ), exists. value( ));

         std::cout << seq << "\n";
         std::cout << "exists = " << exists << "\n";

         auto res = deduce( elim. intro( ), seq, err );
         if( res. has_value( ))
            std::cout << "got " << res. value( ) << "\n";     
#if 0
         if( !iscontradiction( first ))
            throw std::logic_error( "not a contradiction" );

         seq. restore( seqsize );
         std::cout << seq << "\n";

         auto rest = remove( subform( parent, res. conj( )), res. disj( ));
         return replace( parent, res. conj( ), rest );
#endif
         std::cout << "crashing with "; 
         exists. print( std::cout );  
         throw std::logic_error( "exists-elim is not implemented" );
      }

   case prf_forallelim:
      {
         auto elim = prf. view_forallelim( );
         auto anf = deduce( elim. parent( ), seq, err );
         if( !anf. has_value( ))
            return anf;

         auto forall = optform( std::move( anf ), "forall-elim", seq, err );
         forall. musthave( logic::op_kleene_and );
         forall. getsub( elim. nrforall( ));
         forall. musthave( logic::op_kleene_forall );
         forall. nrvarsmustbe( elim. size( )); 
         forall. pretty( std::cout );
         if( !forall. has_value( )) 
            return { };

         size_t errstart = err. size( );
         logic::fullsubst subst;

         auto q = forall. value( ). view_quant( ); 
         for( size_t i = 0; i != elim. size( ); ++ i )
         {
            logic::context ctxt;
            auto tm = elim. value(i);
            auto tp = checkandresolve( seq. blfs, err, ctxt, tm );

            if( tp. has_value( )) 
            {
               if( logic::cmp::equal( tp. value( ), q. var(i). tp ))
               {
                  subst. push( std::move( tm ));
               }
               else
               {
                  auto bld = errorstack::builder( ); 
                  bld << "true type of instance ";
                  logic::context ctxt;
                  logic::pretty::print( bld, seq. blfs, ctxt, tm );
                  bld << " is wrong\n"; 
                  bld << "It is "; 
                  logic::pretty::print( bld, seq. blfs, tp. value( ), {0,0} );
                  bld << ", but must be ";
                  logic::pretty::print( bld, seq. blfs, q. var(i). tp, {0,0} ); 
                  err. push( std::move( bld ));
               }
            }
         }
        
         if( subst. size( ) < elim. size( ))
         {
            auto header = forall. errorheader( );
            err. addheader( errstart, std::move( header )); 
            return { };
         } 
         auto res = outermost( subst, std::move( q. body( )), 0 ); 
         res = logic::term( logic::op_kleene_and, { res } );
         return res; 
      }

   case prf_magic:
      {
         auto res = optform( prf. view_magic( ). goal( ), "magic", seq, err );
         res. make_anf2( );
         res. magic( ); 
         return res. value( ); 
      }

   case prf_show:
      {
         auto show = prf. view_show( ); 
         auto res = deduce( show. prf( ), seq, err );
         std::cout << "------------------------------------------------\n";
         std::cout << "showing " << show. comment( ) << ":\n";
         std::cout << seq << "\n";
         if( res. has_value( ))
         {
            std::cout << "deduced formula: " << res. value( ) << "\n";
         }
         else
            std::cout << "(proof failed)\n";
         std::cout << "\n";
         return res;
      } 
   }

   std::cout << prf. sel( ) << "\n";
   throw std::logic_error( "dont know how to check proof term" );
}


