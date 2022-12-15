/*
  ===============================================
  DCC831 Formal Methods
  2022.2

  Mini Project 2 - Part A

  Your name(s): Alan Cabral Trindade Prado 2020006345
                Artur Gaspar da Silva      2020006388 
  ===============================================
*/


function method rem<T(==)>(x: T, s: seq<T>): seq<T>
    decreases s;
    ensures x !in rem(x, s);
    ensures forall i :: 0 <= i < |rem(x, s)| ==> rem(x, s)[i] in s;
    ensures forall i :: 0 <= i < |s| && s[i] != x ==> s[i] in rem(x, s);
  {
    if s == [] then 
      []
    else if s[0] == x then
      rem(x,s[1..])
    else
      [s[0]]+rem(x,s[1..])
  }

// The next three classes have a minimal class definition,
// for simplicity
class Address
{
  constructor () {}
}

class Date
{
  constructor () {}
}

class MessageId
{
  constructor () {}
}

//==========================================================
//  Message
//==========================================================
class Message
{
  var id: MessageId;
  var content: string;
  var date: Date;
  var sender: Address;
  var recipients: seq<Address>;

  constructor (s: Address)
    ensures fresh(id);
    ensures fresh(date);
    ensures content == "";
    ensures sender == s;
    ensures recipients == [];
  {
    id := new MessageId();
    date := new Date();
    sender := s;
    content := "";
    recipients := [];
  }

  method setContent(c: string)
    modifies this;
    ensures content == c;
  {
    content := c;
  }

  method setDate(d: Date)
    modifies this;
    ensures date == d;
  {
    date := d;
  }

  method addRecipient(p: nat, r: Address)
    modifies this;
    requires p < |recipients|;
    ensures |recipients| == |old(recipients)| + 1;
    ensures recipients[p] == r;
    ensures forall i :: 0 <= i < p ==> recipients[i] == old(recipients[i]);
    ensures forall i :: p < i < |recipients| ==> recipients[i] == old(recipients[i-1]);
  {
    recipients := recipients[..p] + [r] + recipients[p..];
  }
}

//==========================================================
//  Mailbox
//==========================================================
// Each Mailbox has a name, which is a string. Its main content is a set of messages.
class Mailbox {
  var messages: set<Message>;
  var name: string;

  // Creates an empty mailbox with name n
  constructor (n: string)
    ensures name == n;
    ensures messages == {};
  {
    name := n;
    messages := {};
  }

  // Adds message m to the mailbox
  method add(m: Message)
    modifies this
    ensures messages == messages + {m}
  {
    messages := { m } + messages;
  }

  // Removes message m from mailbox
  // m need not be in the mailbox
  method remove(m: Message)
    modifies this
    ensures messages == messages - {m}
  {
    messages := messages - { m };
  }

  // Empties the mailbox messages
  method empty()
    modifies this
    ensures messages == {}
  {
    messages := {};
  }
}

//==========================================================
//  MailApp
//==========================================================
class MailApp {
  // abstract field for user defined boxes
  ghost var userboxes: set<Mailbox>;

  // the inbox, drafts, trash and sent are both abstract and concrete
  var inbox: Mailbox;
  var drafts: Mailbox;
  var trash: Mailbox;
  var sent: Mailbox;

  // userboxList implements userboxes
  var userboxList: seq<Mailbox>;

  // Class invariant
  predicate Valid()
    reads this
  {
    //----------------------------------------------------------
    // Abstract state invariants
    //----------------------------------------------------------
    // all predefined mailboxes (inbox, ..., sent) are distinct
    |{inbox, drafts, trash, sent}| == 4 &&
    // none of the predefined mailboxes are in the set of user-defined mailboxes
    !(exists x:: x in {inbox, drafts, trash, sent} && x in userboxList) &&
    //----------------------------------------------------------
    // Abstract-to-concrete state invariants
    //----------------------------------------------------------
    // userboxes is the set of mailboxes in userboxList
    forall x:: x in userboxes ==> x in userboxList &&
    forall x:: x in userboxList ==> x in userboxes 
  }

  constructor ()
    ensures fresh(inbox)
    ensures fresh(drafts)
    ensures fresh(trash)
    ensures fresh(sent)
    ensures fresh(userboxList)
    ensures Valid()
  {
    inbox := new Mailbox("Inbox");
    drafts := new Mailbox("Drafts");
    trash := new Mailbox("Trash");
    sent := new Mailbox("Sent");
    userboxList := [];
    userboxes := {};
  }

  // Deletes user-defined mailbox mb
  method deleteMailbox(mb: Mailbox)
    modifies this, userboxList
    requires Valid()
    ensures mb !in userboxes
    ensures Valid()
  {
    userboxes := userboxes - {mb};
    userboxList := rem(mb, userboxList);
  }

  // Adds a new mailbox with name n to set of user-defined mailboxes
  // provided that no user-defined mailbox has name n already
  method newMailbox(n: string)
    modifies this, userboxList
    requires Valid()
    requires forall x:: x in userboxList ==> x in userboxes // this is included in Valid(), but for some reason Dafny needs it here to be able to prove everything is ok.
    requires !(exists m:: m in userboxes && m.name == n)
    ensures exists m:: m in userboxes && m.name == n
    ensures Valid()
  {
    var mb := new Mailbox(n);
    userboxList := [mb] + userboxList;
    userboxes := {mb} + userboxes;
  }

  // Adds a new message with sender s to the drafts mailbox
  method newMessage(s: Address)
    modifies this, drafts
    requires Valid()
    ensures exists m:: m in drafts.messages && m.sender == s
    ensures Valid()
  {
    var m := new Message(s);
    drafts.add(m);
  }

  // Moves message m from mailbox mb1 to a different mailbox mb2
  method moveMessage (m: Message, mb1: Mailbox, mb2: Mailbox)
    modifies mb1, mb2
    requires Valid()
    requires mb1 != mb2
    requires m in mb1.messages
    ensures m !in mb1.messages
    ensures m in mb2.messages
    ensures Valid()
  {
    mb1.remove(m);
    mb2.add(m);
  }

  // Moves message m from mailbox mb to the trash mailbox provided
  // that mb is not the trash mailbox
  method deleteMessage (m: Message, mb: Mailbox)
    modifies this, trash, mb
    requires mb != trash
    requires m in mb.messages
    requires Valid()
    ensures m !in mb.messages
    ensures m in trash.messages
    ensures Valid()
  {
    moveMessage(m, mb, trash);
  }

  // Moves message m from the drafts mailbox to the sent mailbox
  method sendMessage(m: Message)
    modifies this, drafts, sent
    requires m in drafts.messages
    requires Valid()
    ensures m !in drafts.messages
    ensures m in sent.messages
    ensures Valid()
  {
    moveMessage(m, drafts, sent);
  }

  // Empties the trash mailbox
  method emptyTrash ()
    modifies this,trash
    requires Valid()
    ensures trash.messages == {}
    ensures Valid()
  {
    trash.empty();
  }
}

