//! # ERC-721
//!
//! This is an ERC-721 Token implementation.
//!
//! ## Warning
//!
//! This contract is an *example*. It is neither audited nor endorsed for production use.
//! Do **not** rely on it to keep anything of value secure.
//!
//! ## Overview
//!
//! This contract demonstrates how to build non-fungible or unique tokens using ink!.
//!
//! ## Error Handling
//!
//! Any function that modifies the state returns a `Result` type and does not changes the
//! state if the `Error` occurs.
//! The errors are defined as an `enum` type. Any other error or invariant violation
//! triggers a panic and therefore rolls back the transaction.
//!
//! ## Token Management
//!
//! After creating a new token, the function caller becomes the owner.
//! A token can be created, transferred, or destroyed.
//!
//! Token owners can assign other accounts for transferring specific tokens on their
//! behalf. It is also possible to authorize an operator (higher rights) for another
//! account to handle tokens.
//!
//! ### Token Creation
//!
//! Token creation start by calling the `mint(&mut self, id: u32)` function.
//! The token owner becomes the function caller. The Token ID needs to be specified
//! as the argument on this function call.
//!
//! ### Token Transfer
//!
//! Transfers may be initiated by:
//! - The owner of a token
//! - The approved address of a token
//! - An authorized operator of the current owner of a token
//!
//! The token owner can transfer a token by calling the `transfer` or `transfer_from`
//! functions. An approved address can make a token transfer by calling the
//! `transfer_from` function. Operators can transfer tokens on another account's behalf or
//! can approve a token transfer for a different account.
//!
//! ### Token Removal
//!
//! Tokens can be destroyed by burning them. Only the token owner is allowed to burn a
//! token.
#[allow(dead_code, unused_variables, unused_comparisons)]
mod erc721 {

    use prusti_contracts::*;

    #[resource_kind]
    struct OwnedTokens(AccountId);

    #[resource_kind]
    struct OwnershipOf(TokenId);

    #[resource_kind]
    struct TokenApproval(TokenId);

    #[extern_spec]
    impl<T: Default> Option<T> {
        #[pure]
        #[ensures(result == matches!(self, None))]
        fn is_none(&self) -> bool;

        #[pure]
        #[ensures(result == matches!(self, Some(_)))]
        fn is_some(&self) -> bool;

        #[pure]
        #[requires(self.is_some())]
        #[ensures(self === Some(result))]
        fn unwrap(self) -> T;

        #[pure]
        #[ensures(self.is_some() ==> result === self.unwrap())]
        #[ensures(!self.is_some() ==> result === Default::default())]
        fn unwrap_or_default(self) -> T;

        #[pure]
        #[ensures(self.is_some() ==> result === self.unwrap())]
        #[ensures(!self.is_some() ==> result === fallback)]
        fn unwrap_or(self, fallback: T) -> T;

        #[pure]
        #[requires(self.is_some())]
        #[ensures(self === Some(result))]
        fn expect(self, msg: &str) -> T;
    }

    type AccountId = u32;

    /// A token ID.
    pub type TokenId = u32;
    struct Mapping<K, V>(u32, std::marker::PhantomData<(K, V)>);

    struct Env(AccountId);

    impl Env {
        #[pure]
        fn caller(&self) -> AccountId {
            self.0
        }
        fn emit_event<T>(&self, event: T) {}
    }

    impl<K: Copy, V: Copy> Mapping<K, V> {
        #[trusted]
        #[ensures(forall(|k : K| result.get(k) === None))]
        #[ensures(forall(|k : K| !result.get(k).is_some()))]
        fn new() -> Self {
            unimplemented!()
        }
    }

    impl<T: Copy, U: Copy> Mapping<T, U> {
        #[trusted]
        #[ensures(self.get(key) === Some(value))]
        #[ensures(self.get(key).is_some())]
        #[ensures(self.get(key).unwrap() === value)]
        #[ensures(forall(|k : T| k !== key ==> self.get(k) === old(self.get(k))))]
        fn insert(&mut self, key: T, value: U) {
            unimplemented!()
        }

        #[trusted]
        #[ensures(self.get(key) === None)]
        #[ensures(forall(|k : T| k !== key ==> self.get(k) === old(self.get(k))))]
        fn remove(&mut self, key: T) {
            unimplemented!()
        }

        #[pure]
        #[trusted]
        fn get(&self, key: T) -> Option<U> {
            unimplemented!()
        }

        #[pure]
        #[trusted]
        #[ensures(result == matches!(self.get(key), Some(_)))]
        fn contains(&self, key: T) -> bool {
            unimplemented!()
        }
    }

    #[invariant_twostate(self.env.caller() === old(self.env.caller()))]
    #[invariant_twostate(
        forall(|a: AccountId|
            holds(OwnedTokens(a)) - old(holds(OwnedTokens(a))) ==
            PermAmount::from(self.balance_of(a)) - PermAmount::from(old(self.balance_of(a)))
        )
    )]
    #[invariant_twostate(
        forall(|t: TokenId|
            (holds(OwnershipOf(t)) == PermAmount::from(0) &&
            old(holds(OwnershipOf(t))) == PermAmount::from(0)) ==>
            self.owner_of(t) === old(self.owner_of(t)), triggers=[(self.owner_of(t))])
    )]
    #[invariant(
        forall(|a: AccountId, t: TokenId|
        self.owner_of(t) === Some(a) ==>
            self.balance_of(a) > 0
        , triggers=[(self.owner_of(t), self.balance_of(a))])
    )]
    #[invariant(
        forall(|t: TokenId|
            holds(TokenApproval(t)) - old(holds(TokenApproval(t))) == PermAmount::from(1) ==>
                self.get_approved(t).is_some()
        )
    )]
    // #[invariant_twostate(
    //     forall(|t: TokenId|
    //         (holds(OwnershipOf(t)) == PermAmount::from(0) &&
    //         old(holds(OwnershipOf(t))) == PermAmount::from(0)) ==>
    //         self.owner_of(t) === old(self.owner_of(t)), triggers=[(self.owner_of(t))])
    // )]
    pub struct Erc721 {
        /// Mapping from token to owner.
        token_owner: Mapping<TokenId, AccountId>,
        /// Mapping from token to approvals users.
        token_approvals: Mapping<TokenId, AccountId>,
        /// Mapping from owner to number of owned token.
        owned_tokens_count: Mapping<AccountId, u32>,
        /// Mapping from owner to operator approvals.
        operator_approvals: Mapping<(AccountId, AccountId), ()>,
        env: Env,
    }

    #[derive(PartialEq, Eq, Copy, Clone)]
    pub enum Error {
        NotOwner,
        NotApproved,
        TokenExists,
        TokenNotFound,
        CannotInsert,
        CannotFetchValue,
        NotAllowed,
    }

    /// Event emitted when a token transfer occurs.
    pub struct Transfer {
        from: Option<AccountId>,
        to: Option<AccountId>,
        id: TokenId,
    }

    /// Event emitted when a token approve occurs.
    pub struct Approval {
        from: AccountId,
        to: AccountId,
        id: TokenId,
    }

    /// Event emitted when an operator is enabled or disabled for an owner.
    /// The operator can manage all NFTs of the owner.
    pub struct ApprovalForAll {
        owner: AccountId,
        operator: AccountId,
        approved: bool,
    }

    impl Erc721 {
        #[pure]
        fn env(&self) -> &Env {
            &self.env
        }

        /// Creates a new ERC-721 token contract.
        #[trusted]
        pub fn new() -> Self {
            unimplemented!()
            // Default::default()
        }

        /// Returns the balance of the owner.
        ///
        /// This represents the amount of unique tokens the owner has.
        #[pure]
        #[ensures(result != 0 ==> self.owned_tokens_count.contains(owner))]
        pub fn balance_of(&self, owner: AccountId) -> u32 {
            self.balance_of_or_zero(owner)
        }

        /// Returns the owner of the token.
        #[pure]
        #[ensures(matches!(result, Some(_)) ==> self.token_exists(id))]
        pub fn owner_of(&self, id: TokenId) -> Option<AccountId> {
            self.token_owner.get(id)
        }

        /// Returns the approved account ID for this token if any.
        #[pure]
        pub fn get_approved(&self, id: TokenId) -> Option<AccountId> {
            self.token_approvals.get(id)
        }

        /// Returns `true` if the operator is approved by the owner.
        pub fn is_approved_for_all(&self, owner: AccountId, operator: AccountId) -> bool {
            self.approved_for_all(owner, operator)
        }

        /// Approves or disapproves the operator for all tokens of the caller.
        pub fn set_approval_for_all(
            &mut self,
            to: AccountId,
            approved: bool,
        ) -> Result<(), Error> {
            self.approve_for_all(to, approved)?;
            Ok(())
        }

        /// Approves the account to transfer the specified token on behalf of the caller.
        pub fn approve(&mut self, to: AccountId, id: TokenId) -> Result<(), Error> {
            self.approve_for(to, id)?;
            Ok(())
        }

        /// Transfers the token from the caller to the given destination.
        #[requires((self.token_owner.get(id) == Some(self.env.caller())) ==> resource(OwnershipOf(id), 1))]
        #[requires((self.token_owner.get(id) == Some(self.env.caller())) ==> resource(OwnedTokens(
            self.env.caller()
        ), 1))]
        #[ensures(result == Ok(()) ==> resource(OwnershipOf(id), 1))]
        #[ensures(result == Ok(()) ==> resource(OwnedTokens(to), 1))]
        pub fn transfer(
            &mut self,
            to: AccountId,
            id: TokenId,
        ) -> Result<(), Error> {
            let caller = self.env.caller();
            if {
                self.token_owner.get(id) == Some(caller)
            } {
                prusti_assert!(self.can_transfer(caller, id));
            }
            self.transfer_token_from(caller, to, id)
        }

        predicate! {
            fn can_transfer(&self, from: AccountId, id: TokenId) -> bool {
                if self.token_exists(id) {
                    let owner = self.owner_of(id);
                        (Some(from) == owner
                            || Some(from) == self.token_approvals.get(id)
                            || self.approved_for_all(
                                owner.unwrap(),
                                from
                            ))
                } else {
                    false
                }
            }
        }

        /// Transfer approved or owned token.
        #[requires(self.token_owner.get(id) == Some(from) && self.can_transfer(self.env.caller(), id) ==> resource(OwnershipOf(id), 1))]
        #[requires(self.token_owner.get(id) == Some(from) && self.can_transfer(self.env.caller(), id) ==> resource(OwnedTokens(
            from
        ), 1))]
        #[ensures(result == Ok(()) ==> resource(OwnershipOf(id), 1))]
        #[ensures(result == Ok(()) ==> resource(OwnedTokens(to), 1))]
        pub fn transfer_from(
            &mut self,
            from: AccountId,
            to: AccountId,
            id: TokenId,
        ) -> Result<(), Error> {
            self.transfer_token_from(from, to, id)
        }

        /// Creates a new token.
        #[ensures(result == Ok(()) ==> resource(OwnershipOf(id), 1))]
        #[ensures(result == Ok(()) ==> resource(OwnedTokens(self.env.caller()), 1))]
        pub fn mint(&mut self, id: TokenId) -> Result<(), Error> {
            let caller = self.env.caller();
            let result = self.add_token_to(caller, id);
            if !matches!(result, Ok(_)) {
                return result;
            }
            // TODO
            // self.env.emit_event(Transfer {
            //     from: Some(0),
            //     to: Some(caller),
            //     id,
            // });
            Ok(())
        }

        /// Deletes an existing token. Only the owner can burn the token.
        #[requires(
            self.owner_of(id) == Some(self.env.caller()) ==>
            resource(OwnershipOf(id), 1)
        )]
        #[requires(
            self.owner_of(id) == Some(self.env.caller()) ==>
            resource(OwnedTokens(self.env.caller()), 1)
        )]
        pub fn burn(&mut self, id: TokenId) -> Result<(), Error> {
            let caller = self.env.caller();

            // Unused but required for triggers
            let owner_orig = self.owner_of(id);
            let balance_orig = self.balance_of(caller);

            prusti_assert!(
        forall(|a: AccountId, t: TokenId|
        self.owner_of(t) === Some(a) ==> self.balance_of(a) > 0
        , triggers=[(self.owner_of(t), self.balance_of(a))]));

            let Self {
                token_owner,
                owned_tokens_count,
                ..
            } = self;

            let owner = token_owner.get(id);
            let owner = match owner {
                Some(owner) => owner,
                None => {
                    return Err(Error::TokenNotFound)
                }
            };
            if owner != caller {
                return Err(Error::NotOwner);
            };

            let count = owned_tokens_count.get(caller);
            prusti_assert!(count.is_some());
            let count = match count {
                Some(count) => count,
                None => {
                    return Err(Error::CannotFetchValue);
                }
            };
            prusti_assert!(count > 0);
            consume!(resource(OwnershipOf(id), 1));
            consume!(resource(OwnedTokens(caller), 1));
            let count = count - 1;

            owned_tokens_count.insert(caller, count);
            token_owner.remove(id);

            // Unused but required for triggers
            let owner_orig = self.owner_of(id);
            let balance_orig = self.balance_of(caller);

            prusti_assume!(
        forall(|a: AccountId, t: TokenId|
        self.owner_of(t) === Some(a) ==> self.balance_of(a) > 0
        , triggers=[(self.owner_of(t), self.balance_of(a))]));

            // TODO
            // self.env.emit_event(Transfer {
            //     from: Some(caller),
            //     to: Some(0),
            //     id,
            // });

            Ok(())
        }

        #[requires(
            (self.owner_of(id) == Some(from) && self.can_transfer(self.env.caller(), id)) ==> resource(OwnershipOf(id), 1))]
        #[requires(
            (self.owner_of(id) == Some(from) && self.can_transfer(self.env.caller(), id)) ==> resource(OwnedTokens(
            from
        ), 1))]
        #[ensures(result == Ok(()) ==> resource(OwnershipOf(id), 1))]
        #[ensures(result == Ok(()) ==> resource(OwnedTokens(to), 1))]
        fn transfer_token_from(
            &mut self,
            from: AccountId,
            to: AccountId,
            id: TokenId,
        ) -> Result<(), Error> {
            let caller = self.env.caller();
            if !self.token_exists(id) {
                return Err(Error::TokenNotFound);
            };
            if !self.approved_or_owner(caller, id) {
                return Err(Error::NotApproved);
            };
            if self.token_owner.get(id) != Some(from) {
                return Err(Error::NotOwner);
            }
            prusti_assert!(self.can_transfer(caller, id));
            self.clear_approval(id);
            let r = self.remove_token_from(from, id);
            if !matches!(r, Ok(_)) {
                return r;
            }
            let r = self.add_token_to(to, id);
            if !matches!(r, Ok(_)) {
                return r;
            }

            // TODO
            // self.env.emit_event(Transfer {
            //     from: Some(*from),
            //     to: Some(*to),
            //     id,
            // });
            Ok(())
        }

        /// Removes token `id` from the owner.
        #[requires(self.owner_of(id) == Some(from))]
        #[requires(resource(OwnershipOf(id), 1))]
        #[requires(resource(OwnedTokens(from), 1))]
        fn remove_token_from(
            &mut self,
            from: AccountId,
            id: TokenId,
        ) -> Result<(), Error> {

            // Unused but required for triggers
            let owner_orig = self.owner_of(id);
            let balance_orig = self.balance_of(from);

            let Self {
                token_owner,
                owned_tokens_count,
                ..
            } = self;

            if !token_owner.contains(id) {
                prusti_assert!(false);
                return Err(Error::TokenNotFound);
            }


            let count = owned_tokens_count.get(from).unwrap();
            let count = count - 1;

            owned_tokens_count.insert(from, count);
            token_owner.remove(id);

            prusti_assume!(
        forall(|a: AccountId, t: TokenId|
        self.owner_of(t) === Some(a) ==> self.balance_of(a) > 0
        , triggers=[(self.owner_of(t), self.balance_of(a))]));

            Ok(())
        }

        /// Adds the token `id` to the `to` AccountID.
        #[ensures(result == Ok(()) ==> resource(OwnershipOf(id), 1))]
        #[ensures(result == Ok(()) ==> resource(OwnedTokens(to), 1))]
        fn add_token_to(&mut self, to: AccountId, id: TokenId) -> Result<(), Error> {
            let Self {
                token_owner,
                owned_tokens_count,
                ..
            } = self;

            if token_owner.contains(id) {
                return Err(Error::TokenExists);
            }

            // TODO
            // if to == 0 {
            //     return Err(Error::NotAllowed);
            // };

            let count = owned_tokens_count.get(to).unwrap_or(0);
            let count = count + 1;

            owned_tokens_count.insert(to, count);
            token_owner.insert(id, to);
            produce!(resource(OwnershipOf(id), 1));
            produce!(resource(OwnedTokens(to), 1));
            prusti_assert!(self.balance_of(to) == count);
            prusti_assert!(self.owner_of(id) == Some(to));
            prusti_assert!(
                forall(|t: TokenId| t != id ==>
                    self.owner_of(t) == old(self.owner_of(t))
                )
            );

            Ok(())
        }

        /// Approves or disapproves the operator to transfer all tokens of the caller.
        fn approve_for_all(
            &mut self,
            to: AccountId,
            approved: bool,
        ) -> Result<(), Error> {
            let caller = self.env.caller();
            if to == caller {
                return Err(Error::NotAllowed);
            }
            self.env.emit_event(ApprovalForAll {
                owner: caller,
                operator: to,
                approved,
            });

            if approved {
                self.operator_approvals.insert((caller, to), ());
            } else {
                self.operator_approvals.remove((caller, to));
            }

            Ok(())
        }

        /// Approve the passed `AccountId` to transfer the specified token on behalf of
        /// the message's sender.
        fn approve_for(&mut self, to: AccountId, id: TokenId) -> Result<(), Error> {
            let caller = self.env.caller();
            let owner = self.owner_of(id).ok_or(Error::TokenNotFound)?;
            if !(owner == caller || self.approved_for_all(owner, caller)) {
                return Err(Error::NotAllowed)
            };

            if to == 0 {
                return Err(Error::NotAllowed);
            };

            if self.token_approvals.contains(id) {
                return Err(Error::CannotInsert);
            } else {
                self.token_approvals.insert(id, to);
            }

            // TODO
            // self.env.emit_event(Approval {
            //     from: caller,
            //     to,
            //     id,
            // });

            Ok(())
        }

        /// Removes existing approval from token `id`.
        fn clear_approval(&mut self, id: TokenId) {
            self.token_approvals.remove(id);
        }

        // Returns the total number of tokens from an account.
        #[pure]
        fn balance_of_or_zero(&self, of: AccountId) -> u32 {
            self.owned_tokens_count.get(of).unwrap_or(0)
        }

        /// Gets an operator on other Account's behalf.
        #[pure]
        fn approved_for_all(&self, owner: AccountId, operator: AccountId) -> bool {
            self.operator_approvals.contains((owner, operator))
        }

        /// Returns true if the `AccountId` `from` is the owner of token `id`
        /// or it has been approved on behalf of the token `id` owner.
        #[pure]
        #[requires(0 <= id)] // WHY???
        #[requires(matches!(self.owner_of(id), Some(_)))]
        fn approved_or_owner(&self, from: AccountId, id: TokenId) -> bool {
            let owner = self.owner_of(id);
                Some(from) == owner
                    || Some(from) == self.token_approvals.get(id)
                    || self.approved_for_all(
                        owner.unwrap(),
                        from,
                    )
        }

        /// Returns true if token `id` exists or false if it does not.
        #[pure]
        fn token_exists(&self, id: TokenId) -> bool {
            self.token_owner.contains(id)
        }
    }

    /// Unit tests
    #[cfg(test)]
    mod tests {
        /// Imports all the definitions from the outer scope so we can use them here.
        use super::*;

        fn mint_works() {
            let accounts =
                ink::env::test::default_accounts::<ink::env::DefaultEnvironment>();
            // Create a new contract instance.
            let mut erc721 = Erc721::new();
            // Token 1 does not exists.
            assert_eq!(erc721.owner_of(1), None);
            // Alice does not owns tokens.
            assert_eq!(erc721.balance_of(accounts.alice), 0);
            // Create token Id 1.
            assert_eq!(erc721.mint(1), Ok(()));
            // Alice owns 1 token.
            assert_eq!(erc721.balance_of(accounts.alice), 1);
        }

        fn mint_existing_should_fail() {
            let accounts =
                ink::env::test::default_accounts::<ink::env::DefaultEnvironment>();
            // Create a new contract instance.
            let mut erc721 = Erc721::new();
            // Create token Id 1.
            assert_eq!(erc721.mint(1), Ok(()));
            // The first Transfer event takes place
            assert_eq!(1, ink::env::test::recorded_events().count());
            // Alice owns 1 token.
            assert_eq!(erc721.balance_of(accounts.alice), 1);
            // Alice owns token Id 1.
            assert_eq!(erc721.owner_of(1), Some(accounts.alice));
            // Cannot create  token Id if it exists.
            // Bob cannot own token Id 1.
            assert_eq!(erc721.mint(1), Err(Error::TokenExists));
        }

        fn transfer_works() {
            let accounts =
                ink::env::test::default_accounts::<ink::env::DefaultEnvironment>();
            // Create a new contract instance.
            let mut erc721 = Erc721::new();
            // Create token Id 1 for Alice
            assert_eq!(erc721.mint(1), Ok(()));
            // Alice owns token 1
            assert_eq!(erc721.balance_of(accounts.alice), 1);
            // Bob does not owns any token
            assert_eq!(erc721.balance_of(accounts.bob), 0);
            // The first Transfer event takes place
            assert_eq!(1, ink::env::test::recorded_events().count());
            // Alice transfers token 1 to Bob
            assert_eq!(erc721.transfer(accounts.bob, 1), Ok(()));
            // The second Transfer event takes place
            assert_eq!(2, ink::env::test::recorded_events().count());
            // Bob owns token 1
            assert_eq!(erc721.balance_of(accounts.bob), 1);
        }

        fn invalid_transfer_should_fail() {
            let accounts =
                ink::env::test::default_accounts::<ink::env::DefaultEnvironment>();
            // Create a new contract instance.
            let mut erc721 = Erc721::new();
            // Transfer token fails if it does not exists.
            assert_eq!(erc721.transfer(accounts.bob, 2), Err(Error::TokenNotFound));
            // Token Id 2 does not exists.
            assert_eq!(erc721.owner_of(2), None);
            // Create token Id 2.
            assert_eq!(erc721.mint(2), Ok(()));
            // Alice owns 1 token.
            assert_eq!(erc721.balance_of(accounts.alice), 1);
            // Token Id 2 is owned by Alice.
            assert_eq!(erc721.owner_of(2), Some(accounts.alice));
            // Set Bob as caller
            set_caller(accounts.bob);
            // Bob cannot transfer not owned tokens.
            assert_eq!(erc721.transfer(accounts.eve, 2), Err(Error::NotApproved));
        }

        fn approved_transfer_works() {
            let accounts =
                ink::env::test::default_accounts::<ink::env::DefaultEnvironment>();
            // Create a new contract instance.
            let mut erc721 = Erc721::new();
            // Create token Id 1.
            assert_eq!(erc721.mint(1), Ok(()));
            // Token Id 1 is owned by Alice.
            assert_eq!(erc721.owner_of(1), Some(accounts.alice));
            // Approve token Id 1 transfer for Bob on behalf of Alice.
            assert_eq!(erc721.approve(accounts.bob, 1), Ok(()));
            // Set Bob as caller
            set_caller(accounts.bob);
            // Bob transfers token Id 1 from Alice to Eve.
            assert_eq!(
                erc721.transfer_from(accounts.alice, accounts.eve, 1),
                Ok(())
            );
            // TokenId 3 is owned by Eve.
            assert_eq!(erc721.owner_of(1), Some(accounts.eve));
            // Alice does not owns tokens.
            assert_eq!(erc721.balance_of(accounts.alice), 0);
            // Bob does not owns tokens.
            assert_eq!(erc721.balance_of(accounts.bob), 0);
            // Eve owns 1 token.
            assert_eq!(erc721.balance_of(accounts.eve), 1);
        }

        fn approved_for_all_works() {
            let accounts =
                ink::env::test::default_accounts::<ink::env::DefaultEnvironment>();
            // Create a new contract instance.
            let mut erc721 = Erc721::new();
            // Create token Id 1.
            assert_eq!(erc721.mint(1), Ok(()));
            // Create token Id 2.
            assert_eq!(erc721.mint(2), Ok(()));
            // Alice owns 2 tokens.
            assert_eq!(erc721.balance_of(accounts.alice), 2);
            // Approve token Id 1 transfer for Bob on behalf of Alice.
            assert_eq!(erc721.set_approval_for_all(accounts.bob, true), Ok(()));
            // Bob is an approved operator for Alice
            assert!(erc721.is_approved_for_all(accounts.alice, accounts.bob));
            // Set Bob as caller
            set_caller(accounts.bob);
            // Bob transfers token Id 1 from Alice to Eve.
            assert_eq!(
                erc721.transfer_from(accounts.alice, accounts.eve, 1),
                Ok(())
            );
            // TokenId 1 is owned by Eve.
            assert_eq!(erc721.owner_of(1), Some(accounts.eve));
            // Alice owns 1 token.
            assert_eq!(erc721.balance_of(accounts.alice), 1);
            // Bob transfers token Id 2 from Alice to Eve.
            assert_eq!(
                erc721.transfer_from(accounts.alice, accounts.eve, 2),
                Ok(())
            );
            // Bob does not own tokens.
            assert_eq!(erc721.balance_of(accounts.bob), 0);
            // Eve owns 2 tokens.
            assert_eq!(erc721.balance_of(accounts.eve), 2);
            // Remove operator approval for Bob on behalf of Alice.
            set_caller(accounts.alice);
            assert_eq!(erc721.set_approval_for_all(accounts.bob, false), Ok(()));
            // Bob is not an approved operator for Alice.
            assert!(!erc721.is_approved_for_all(accounts.alice, accounts.bob));
        }

        fn not_approved_transfer_should_fail() {
            let accounts =
                ink::env::test::default_accounts::<ink::env::DefaultEnvironment>();
            // Create a new contract instance.
            let mut erc721 = Erc721::new();
            // Create token Id 1.
            assert_eq!(erc721.mint(1), Ok(()));
            // Alice owns 1 token.
            assert_eq!(erc721.balance_of(accounts.alice), 1);
            // Bob does not owns tokens.
            assert_eq!(erc721.balance_of(accounts.bob), 0);
            // Eve does not owns tokens.
            assert_eq!(erc721.balance_of(accounts.eve), 0);
            // Set Eve as caller
            set_caller(accounts.eve);
            // Eve is not an approved operator by Alice.
            assert_eq!(
                erc721.transfer_from(accounts.alice, accounts.frank, 1),
                Err(Error::NotApproved)
            );
            // Alice owns 1 token.
            assert_eq!(erc721.balance_of(accounts.alice), 1);
            // Bob does not owns tokens.
            assert_eq!(erc721.balance_of(accounts.bob), 0);
            // Eve does not owns tokens.
            assert_eq!(erc721.balance_of(accounts.eve), 0);
        }

        fn burn_works() {
            let accounts =
                ink::env::test::default_accounts::<ink::env::DefaultEnvironment>();
            // Create a new contract instance.
            let mut erc721 = Erc721::new();
            // Create token Id 1 for Alice
            assert_eq!(erc721.mint(1), Ok(()));
            // Alice owns 1 token.
            assert_eq!(erc721.balance_of(accounts.alice), 1);
            // Alice owns token Id 1.
            assert_eq!(erc721.owner_of(1), Some(accounts.alice));
            // Destroy token Id 1.
            assert_eq!(erc721.burn(1), Ok(()));
            // Alice does not owns tokens.
            assert_eq!(erc721.balance_of(accounts.alice), 0);
            // Token Id 1 does not exists
            assert_eq!(erc721.owner_of(1), None);
        }

        fn burn_fails_token_not_found() {
            // Create a new contract instance.
            let mut erc721 = Erc721::new();
            // Try burning a non existent token
            assert_eq!(erc721.burn(1), Err(Error::TokenNotFound));
        }

        fn burn_fails_not_owner() {
            let accounts =
                ink::env::test::default_accounts::<ink::env::DefaultEnvironment>();
            // Create a new contract instance.
            let mut erc721 = Erc721::new();
            // Create token Id 1 for Alice
            assert_eq!(erc721.mint(1), Ok(()));
            // Try burning this token with a different account
            set_caller(accounts.eve);
            assert_eq!(erc721.burn(1), Err(Error::NotOwner));
        }

        fn set_caller(sender: AccountId) {
            ink::env::test::set_caller::<ink::env::DefaultEnvironment>(sender);
        }
    }
}

fn main() {}
