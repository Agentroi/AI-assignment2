## Belief Revision Agent
Make sure to download and install ``sympy`` in your environment. You can run the ``belief_revision_agent`` by running it as a script. 

First, you need to initialize your knowledge base. Write a belief, then enter. Thereafter input a priority for the belief. The syntax is as following:

``'p & q' for 'p AND q', 'p | q' for 'p OR q', and '~p' for 'NOT p'. For equivalance, use Equvialent(p,q) and for implication, use p >> q ``

Thereafter you can choose an action from the following list:
Select an action:
1. Add a new belief to the belief base
2. Perform a resolution on the belief base
3. Contract a belief from the belief base
4. Revise the belief base
5. Exit

The interface will otherwise prompt you, while using the system. 