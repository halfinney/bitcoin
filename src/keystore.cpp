// Copyright (c) 2009-2010 Satoshi Nakamoto
// Copyright (c) 2009-2012 The Bitcoin developers
// Distributed under the MIT/X11 software license, see the accompanying
// file COPYING or http://www.opensource.org/licenses/mit-license.php.

#include "keystore.h"
#include "script.h"

bool CKeyStore::GetPubKey(const CKeyID &address, CPubKey &vchPubKeyOut) const
{
    CKey key;
    if (!GetKey(address, key))
        return false;
    vchPubKeyOut = key.GetPubKey();
    return true;
}

bool CBasicKeyStore::AddKey(const CKey& key)
{
    bool fCompressed = false;
    CSecret secret = key.GetSecret(fCompressed);
    {
        LOCK(cs_KeyStore);
        mapKeys[key.GetPubKey().GetID()] = make_pair(secret, fCompressed);
    }
    return true;
}

bool CBasicKeyStore::AddCScript(const CScript& redeemScript)
{
    {
        LOCK(cs_KeyStore);
        mapScripts[redeemScript.GetID()] = redeemScript;
    }
    return true;
}

bool CBasicKeyStore::HaveCScript(const CScriptID& hash) const
{
    bool result;
    {
        LOCK(cs_KeyStore);
        result = (mapScripts.count(hash) > 0);
    }
    return result;
}


bool CBasicKeyStore::GetCScript(const CScriptID &hash, CScript& redeemScriptOut) const
{
    {
        LOCK(cs_KeyStore);
        ScriptMap::const_iterator mi = mapScripts.find(hash);
        if (mi != mapScripts.end())
        {
            redeemScriptOut = (*mi).second;
            return true;
        }
    }
    return false;
}

bool CCryptoKeyStore::SetCrypted()
{
    {
        LOCK(cs_KeyStore);
        if (fUseCrypto)
            return true;
        if (!mapKeys.empty())
            return false;
        fUseCrypto = true;
    }
    return true;
}

bool CCryptoKeyStore::AddKey(const CKey& key)
{
    {
        LOCK(cs_KeyStore);
        if (!IsCrypted())
            return CBasicKeyStore::AddKey(key);

        if (IsLocked())
            return false;

        std::vector<unsigned char> vchCryptedSecret;
        CPubKey vchPubKey = key.GetPubKey();
        bool fCompressed;
        if (!EncryptSecret(key.GetSecret(fCompressed), vchPubKey.GetHash(), vchCryptedSecret))
            return false;
#if 0
        fprintf(stdout, "pk:\n");
        for (unsigned i=0; i<vchPubKey.Raw().size(); i++)
            fprintf(stdout, "%02x%s", vchPubKey.Raw()[i], ((i+1)%16)?" ":"\n");
        if (vchPubKey.Raw().size()%16)
            fprintf(stdout, "\n");
#endif

        if (!AddCryptedKey(key.GetPubKey(), vchCryptedSecret))
            return false;
    }
    return true;
}


bool CCryptoKeyStore::AddCryptedKey(const CPubKey &vchPubKey, const std::vector<unsigned char> &vchCryptedSecret)
{
    {
        LOCK(cs_KeyStore);
        if (!SetCrypted())
            return false;

        mapCryptedKeys[vchPubKey.GetID()] = make_pair(vchPubKey, vchCryptedSecret);
    }
    return true;
}

bool CCryptoKeyStore::GetCryptedKey(const CPubKey &vchPubKey, std::vector<unsigned char> &vchCryptedSecret) const
{
    {
        LOCK(cs_KeyStore);
        if (!IsCrypted())
            return false;

        CKeyID address = vchPubKey.GetID();
        CryptedKeyMap::const_iterator mi = mapCryptedKeys.find(address);
        if (mi == mapCryptedKeys.end())
            return false;
        vchCryptedSecret = (*mi).second.second;
    }
    return true;
}

bool CCryptoKeyStore::GetKey(const CKeyID &address, CKey& keyOut) const
{
    {
        LOCK(cs_KeyStore);
        if (!IsCrypted())
            return CBasicKeyStore::GetKey(address, keyOut);

        CryptedKeyMap::const_iterator mi = mapCryptedKeys.find(address);
        if (mi != mapCryptedKeys.end())
        {
            const CPubKey &vchPubKey = (*mi).second.first;
            const std::vector<unsigned char> &vchCryptedSecret = (*mi).second.second;
            CSecret vchSecret;
            if (!DecryptSecret(vchCryptedSecret, vchPubKey.GetHash(), vchSecret))
                return false;
            if (vchSecret.size() != 32)
                return false;
            keyOut.SetPubKey(vchPubKey);
            keyOut.SetSecret(vchSecret);
#if 0
            fprintf(stdout, "pk:\n");
            for (unsigned i=0; i<vchPubKey.Raw().size(); i++)
                fprintf(stdout, "%02x%s", vchPubKey.Raw()[i], ((i+1)%16)?" ":"\n");
            if (vchPubKey.Raw().size()%16)
                fprintf(stdout, "\n");
#endif
            return true;
        }
    }
    return false;
}

bool CCryptoKeyStore::GetPubKey(const CKeyID &address, CPubKey& vchPubKeyOut) const
{
    {
        LOCK(cs_KeyStore);
        if (!IsCrypted())
            return CKeyStore::GetPubKey(address, vchPubKeyOut);

        CryptedKeyMap::const_iterator mi = mapCryptedKeys.find(address);
        if (mi != mapCryptedKeys.end())
        {
            vchPubKeyOut = (*mi).second.first;
            return true;
        }
    }
    return false;
}

bool CCryptoKeyStore::EncryptKeys()
{
    {
        LOCK(cs_KeyStore);
        if (!mapCryptedKeys.empty() || IsCrypted())
            return false;

        fUseCrypto = true;
        BOOST_FOREACH(KeyMap::value_type& mKey, mapKeys)
        {
            CKey key;
            if (!key.SetSecret(mKey.second.first, mKey.second.second))
                return false;
            const CPubKey vchPubKey = key.GetPubKey();
            std::vector<unsigned char> vchCryptedSecret;
            bool fCompressed;
            if (!EncryptSecret(key.GetSecret(fCompressed), vchPubKey.GetHash(), vchCryptedSecret))
                return false;
#if 0
            fprintf(stdout, "pk:\n");
            for (unsigned i=0; i<vchPubKey.Raw().size(); i++)
                fprintf(stdout, "%02x%s", vchPubKey.Raw()[i], ((i+1)%16)?" ":"\n");
            if (vchPubKey.Raw().size()%16)
#endif
                fprintf(stdout, "\n");
            if (!AddCryptedKey(vchPubKey, vchCryptedSecret))
                return false;
        }
        mapKeys.clear();
    }
    return true;
}
