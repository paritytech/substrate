# Pallet Post

A pallet for storing posts on-chain.

## Overview

This is most similar to `remark`, where a user can post some arbitrary comment, but unlike remarks the data in the `pallet-post` gets stored on chain. This will allow 3rd party developers to bootstrap a number of scenarios on top of Substrate based networks without needing to create custom pallets.

In order to avoid post conflicts, all posts are gated by two keys: AccountId and Topic. There are two kinds of posts depending on the ordering of these keys:

* Blogs: Account -> Topic -> Post
* Threads: Topic -> Account -> Post

The idea of threads is that many users may want to make a post on a shared topic, just like a forum thread. In this kind of post format, you can easily query all of the topics that are open for discussion, and then the accounts that have commented on that topic and made a post.

The idea of blogs is that a user may want to make a post on a number of different topics, just like a personal blog. In this kind of post format, you can easily query all the posts from a user by querying for all the blogs under an Account, which will give you a list of topics, and finally the underlying post.

Users will pay a deposit based on the number of bytes used in their topic + post. To return that deposit, users simply need to delete their post.

Posts include a block_number so they may be easily sorted and presented to the outside world.

## Scenarios

* We want to make a poll where on-chain users will provide feedback about some general topic. Off-chain we will define a certain "topic" for discussion, and a format for how users should make a post (for example sending `0x00` for nay and `0x01` for aye. Then users can make a post under that thread for the duration of the polling time. At the end of the polling time, a snapshot of the chain and the current votes can be tallied, with any filtering applied off-chain (for example a filter for only accounts with identities or a weighting factor based on number of tokens held at the end of the poll time. As long as these criteria are made public, anyone else could trustlessly verify the results.

* We want to create a "profile page" for all validators to make comments about their validator setup and why users should vote for them. Here we make another topic under a thread where anyone can make a post using some defined format. Then a service like Polkadot JS could query all the pages under this thread, filtering for users who are in the staking pool, and show this information for each user.

* I may want to make a series of personal posts about things happening on the network. I would add a new topic under my blogs for each of my comments. I could then host a page which queries and presents all of these posts under my account. I could also use this mechanism as a simple way to index into my posts in other threads. For example, I can make a post in a thread under a certain topic, and in my blog place a simple indicator like `0x01` under the same topic so show that if you look at the thread, you would find my post. (i.e. `account -> topic -> "0x01"` could imply that `topic -> account -> post exists`

* Users could post on chain details about some democracy proposal, or whether they support such a proposal using posts, in addition to depending on 3rd party services.
