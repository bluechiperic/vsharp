module Bank

type Money = Int where self >= 0

type Account = { id: Int, balance: Money }

type Accounts = { source: Account, target: Account }

type TransferError = | InsufficientFunds(short: Int) | SameAccount

fn transfer(src: Account, dst: Account, amount: Money) -> Result[Accounts, TransferError]
  ensures match result { Ok(moved) => src.id != dst.id && moved.source.balance + moved.target.balance == src.balance + dst.balance, Err(e) => true }
  ensures src.id != dst.id && amount <= src.balance ==> match result { Ok(m) => true, Err(e) => false }
{
  if src.id == dst.id { return Err(SameAccount) }
  if amount > src.balance { return Err(InsufficientFunds(short: amount - src.balance)) }
  let new_src = Account(id: src.id, balance: src.balance - amount)
  let new_dst = Account(id: dst.id, balance: dst.balance + amount)
  return Ok(Accounts(source: new_src, target: new_dst))
}

fn pay_invoice(customer: Account, shop: Account, invoice: Int, credit: Int) -> Result[Accounts, TransferError]
  requires 0 <= credit && credit <= invoice
{
  return transfer(src: customer, dst: shop, amount: invoice - credit)
}

fn main() -> Unit effects io {
  let alice = Account(id: 1, balance: 100)
  let shop = Account(id: 2, balance: 0)
  print pay_invoice(customer: alice, shop: shop, invoice: 30, credit: 5)
  print pay_invoice(customer: alice, shop: shop, invoice: 500, credit: 0)
  print pay_invoice(customer: alice, shop: alice, invoice: 30, credit: 0)
}
