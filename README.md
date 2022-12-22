# Oblivious Message Retrieval (OMR)

As the name suggests it enables an un-trusted server to detect messages pertaining to you and pack them into a digest obliviously. This means the server learns nothing about which of the messages from set of all messages are present in the digest.

OMR is useful in several scenarios but two of are noteworthy

-   **Transactions retrieval on privacy focused chains (aztec, zcash, penumbra, anoma, aleo)**: Transactions on such chains are, by definition, encrypted. Unlike transactions on Ethereum, receiver's and sender's info is kept private. This raises the following question: how does one detect transactions pertaining to them? If you are running a node of any of these chains and have access to all transactions you can simply run trial decryption on all transactions to check pertinency. However, the solution for mobile wallets/light clients does not look so simple. Today different private chains tackle it in different ways, but all follow the same following concept: download data representative of all transactions and perform trial decryption to check which transactions belong to the user. For example, in Zcash the wallet downloads shielded transactions metadata from the lightwalld server and performs trial decryption to detect which of the transactions belong the user. Then requests these transactions from the server.
    There are two problems with this. (1) User leaks their transactions of interest to the server upon second query. (2) Since light client needs to download and process data representative of all transactions, data size increases with traffic. This makes trial decryption expensive on light client after a point.
    With OMR light clients can assign 3rd party servers with the task of detecting transaction pertaining to them, pack pertaining transactions into a digest, and send the digest. For obvious reasons, this is done obliviously.
-   **Receiver privacy in messaging apps**: To support asynchronous communication between users messaging apps need to store undelivered messages on the server with some related metadata (at-least receiver's and sender's details). Metadata on (encrypted) message exchanges can leak a lot of information, often leading to privacy violation and surprises. Even though apps may promise that they never log metadata for more time than required, it is always a better policy to trust cryptography than to trust a company. That's why Signal introduced "[sealed sender](https://signal.org/blog/sealed-sender/)", enabling you to send message packets asynchronously without the "from" field on message envelope . Now can we take this a step further ? How about removing the "to" field as well ?
    We can achieve this using OMR. Message sender can send the encrypted message with an embedded "clue" (more on this below) to the server. The server will periodically process all received messages and obliviously generate a digest containing messages pertaining to a specific user. Users can then request their digests from the server.

## How does it work ?

Throughout you will find me using words like detection key, clue, public key, message digest, server, and client. So first lets define them

1. Server: Untrusted 3rd party that performs oblivious message retrieval for you. In blockchain context, it's the server that stores up to date set of all transactions and obliviously generates a digest of transactions pertaining to you. In messaging context, it's the app server.
2. Client: You/the user of the app.
3. Message: Data being sent to receiver from sender. In blockchain context, think of transactions as messages.
4. Detection key: Oblivious message retrieval consists of following two tasks (1) Oblivious message detection: Detecting whether a message is pertinent or not. (2) Packing all pertinent messages into the final message digest.
   Detection key is uploaded by the client to the server to aid server in oblivious detection. Note that detection key is un-linkable and does not reveal anything about the client. Client can choose to use a mixer to upload key to the server.
5. Public key: Client generates a public key and posts it on the internet. Anyone can use this public key to indicate to the server that this message is for the client. This is done by generating a clue using the public key and embedding the clue with message before sending it to the server.
6. Clue: To send a message to someone, the sender needs to embed the message with a clue. Servers process clues obliviously to detect whether a message is pertinent to a client or not.

Let's consider Alice, who is a heavy Aztec user and cares a lot about her privacy. She cannot keep track of all transactions sent to aztec to find which ones belong to her. So she relies on a server that periodically generates a data blob of all transactions and sends it to her phone. Her phone then runs trial decryption to identify transactions of interest. But since Aztec has witnessed in an uptick in traffic recently, the data blob has increased and it takes quiet long for Alice's phone to process it.

Server comes to Alice's rescue, by enabling Oblivious message retrieval. All Alice has to do is generate and upload "detection key" to the server and post a "public key" online. Anyone wanting to address Alice in a transaction can use Alice's public key to generate a clue, embed the clue with the transaction, and upload it to the server. The server maintains a public board consisting a set of all transactions, with their respective clues. Server will periodically process the clues on public board using Alice's detection key. It first detects pertaining transactions and then pack them into a digest, using homomorphic encryption. Alice can then request the digest from the server and decrypt to find all transactions sent to her.

## Demo

> Note that you must have `rust` installed.

To run, clone this repository and navigate inside it. Then type `cargo run --release -- -g`.

> `-g` flag is required when running for the first time to generate sample transactions and clues.

For the demo, transactions set size is set to `2^14` and we have assumed `50` are pertinent to the client.

On performance, server processing takes around 120s and client processing takes around 100ms on `apple-m1`. I don't have numbers on intel cpus, so if you happen to have x86 device do keep posted. I think the performance will be worse than `m1`. However this should change in coming days as I add support for SIMD operations to the underlying FHE library used in this repo. More info on this [here](https://github.com/Janmajayamall/fhe.rs)

## Credits

1. Oblivious message retrieval is implementation of OMRp1 from paper by [Zeyu Liu and Eran Tromer](https://eprint.iacr.org/2021/1256.pdf).
2. This repository uses [fork](https://github.com/Janmajayamall/fhe.rs) of [fhe.rs](https://github.com/tlepoint/fhe.rs) for operations on encrypted data.
